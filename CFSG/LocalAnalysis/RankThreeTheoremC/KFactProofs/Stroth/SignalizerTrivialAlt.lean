module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714AltAut

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open MulAction Equiv Subgroup
open scoped Pointwise
open CFSG.GH74.GLS.IVK.Proofs2

namespace AltCore

section Generic

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_relIndex_sup_of_normal (S N : Subgroup G) [N.Normal] :
    S.relIndex N = S.relIndex (S ⊔ N) := by
  have h1 : N.relIndex (S ⊔ N) = N.relIndex S := Subgroup.relIndex_sup_right S N
  have h2 := Subgroup.relIndex_mul_card S N
  have h3 := Subgroup.relIndex_mul_card S (S ⊔ N)
  have h4 := Subgroup.relIndex_mul_card N (S ⊔ N)
  have h5 := Subgroup.relIndex_mul_card N S
  rw [inf_eq_left.mpr le_sup_left] at h3
  rw [inf_eq_left.mpr le_sup_right, h1] at h4
  rw [inf_comm N S] at h5
  have hs : 0 < Nat.card S := Nat.card_pos
  have hd : 0 < Nat.card ↥(S ⊓ N) := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hs hd)
  calc S.relIndex N * (Nat.card S * Nat.card ↥(S ⊓ N))
      = Nat.card N * Nat.card S := by rw [← h2]; ring
    _ = (N.relIndex S * Nat.card ↥(S ⊓ N)) * Nat.card N := by rw [h5]; ring
    _ = (N.relIndex S * Nat.card N) * Nat.card ↥(S ⊓ N) := by ring
    _ = Nat.card ↥(S ⊔ N) * Nat.card ↥(S ⊓ N) := by rw [h4]
    _ = (S.relIndex (S ⊔ N) * Nat.card S) * Nat.card ↥(S ⊓ N) := by rw [h3]
    _ = S.relIndex (S ⊔ N) * (Nat.card S * Nat.card ↥(S ⊓ N)) := by ring

theorem ncard_orbit_normal_dvd {X : Type} [MulAction G X] (N : Subgroup G) [N.Normal] (x : X) :
    (orbit N x).ncard ∣ (orbit G x).ncard := by
  have key : (stabilizer G x).subgroupOf N = stabilizer N x := by
    ext; rfl
  rw [← index_stabilizer G x, ← index_stabilizer N x, ← key]
  change (stabilizer G x).relIndex N ∣ _
  rw [relIndex_eq_relIndex_sup_of_normal]
  rw [← Subgroup.relIndex_mul_index
    (le_sup_left : stabilizer G x ≤ stabilizer G x ⊔ N)]
  exact dvd_mul_right _ _

end Generic

section Orbits

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem not_sq_dvd_factorial {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ∣ p.factorial := by
  intro h
  have h1 : p * p ∣ p * (p - 1).factorial := by
    rw [Nat.mul_factorial_pred hp.ne_zero, ← sq]
    exact h
  have h2 : p ∣ (p - 1).factorial := Nat.dvd_of_mul_dvd_mul_left hp.pos h1
  rw [hp.dvd_factorial] at h2
  have := hp.two_le
  omega

theorem minFac_pow_eq {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) : (p ^ a).minFac = p := by
  have hne : p ^ a ≠ 1 := by
    intro h
    have := Nat.one_lt_pow ha hp.one_lt
    omega
  have hmf := Nat.minFac_prime hne
  have hdvd : (p ^ a).minFac ∣ p := hmf.dvd_of_dvd_pow (Nat.minFac_dvd _)
  exact (Nat.prime_dvd_prime_iff_eq hmf hp).mp hdvd

theorem mem_orbit_subgroup_iff {P : Subgroup (Perm Ω)} {a v : Ω} :
    v ∈ orbit P a ↔ ∃ g ∈ P, g a = v :=
  ⟨fun ⟨g, hg⟩ => ⟨g, g.2, hg⟩, fun ⟨g, hg, h⟩ => ⟨⟨g, hg⟩, h⟩⟩

theorem orbit_subgroupOf_eq {H K : Subgroup (Perm Ω)} (hHK : H ≤ K) (z : Ω) :
    orbit (H.subgroupOf K) z = orbit H z := by
  ext v
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨⟨(n : Perm Ω), Subgroup.mem_subgroupOf.mp n.2⟩, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨⟨(h : Perm Ω), hHK h.2⟩, h.2⟩, rfl⟩

theorem ncard_orbit_pow {p : ℕ} [Fact p.Prime] {P : Subgroup (Perm Ω)} (hP : IsPGroup p P)
    (u : Ω) : ∃ k : ℕ, (orbit P u).ncard = p ^ k := by
  obtain ⟨k, hk⟩ := hP.card_orbit u
  exact ⟨k, by rw [← Nat.card_coe_set_eq]; exact hk⟩

theorem ncard_orbit_eq_p {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hΩ : Nat.card Ω = 2 * p)
    {P : Subgroup (Perm Ω)} (hP : IsPGroup p P) (hPp : p ^ 2 ∣ Nat.card P) (u : Ω) :
    (orbit P u).ncard = p := by
  have hp1 : 1 < p := by omega
  have hsize : ∀ v : Ω, (orbit P v).ncard = 1 ∨ (orbit P v).ncard = p := by
    intro v
    obtain ⟨k, hk⟩ := ncard_orbit_pow hP v
    have hle : (orbit P v).ncard ≤ Nat.card Ω := by
      rw [← Set.ncard_univ]
      exact Set.ncard_le_ncard (Set.subset_univ _)
    rw [hΩ, hk] at hle
    rw [hk]
    rcases k with _ | _ | k
    · simp
    · simp
    · exfalso
      have h1 : p ^ 2 ≤ p ^ (k + 1 + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
  have hnofix : ∀ z : Ω, (orbit P z).ncard ≠ 1 := by
    intro z hz
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hz
    obtain ⟨x, hx⟩ : ∃ x : Ω, (orbit P x).ncard ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hbot : P = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro g hg
        apply Equiv.ext
        intro v
        obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp (hcon v)
        have h1 : g v ∈ orbit P v := mem_orbit_subgroup_iff.mpr ⟨g, hg, rfl⟩
        have h2 : v ∈ orbit P v := mem_orbit_self v
        rw [hb, Set.mem_singleton_iff] at h1 h2
        rw [Equiv.Perm.one_apply, h1, h2]
      rw [hbot, Subgroup.card_bot] at hPp
      have := Nat.le_of_dvd one_pos hPp
      nlinarith
    have hxp : (orbit P x).ncard = p := (hsize x).resolve_left hx
    have hzO : z ∈ (orbit P x)ᶜ := by
      intro hzO
      have heq : orbit P z = orbit P x := MulAction.orbit_eq_iff.mpr hzO
      rw [heq, hxp] at hz
      omega
    have hCcard : (orbit P x)ᶜ.ncard = p := by
      have h := Set.ncard_add_ncard_compl (orbit P x)
      rw [hΩ, hxp] at h
      omega
    have hOinv : ∀ g ∈ P, ∀ v, v ∈ orbit P x ↔ g v ∈ orbit P x := by
      intro g hg v
      constructor
      · intro hv
        obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup_iff.mp hv
        exact mem_orbit_subgroup_iff.mpr ⟨g * k, mul_mem hg hk, by rw [Equiv.Perm.mul_apply]⟩
      · intro hv
        obtain ⟨k, hk, hkv⟩ := mem_orbit_subgroup_iff.mp hv
        refine mem_orbit_subgroup_iff.mpr ⟨g⁻¹ * k, mul_mem (inv_mem hg) hk, ?_⟩
        rw [Equiv.Perm.mul_apply, hkv]
        simp
    have hCfix : ∀ y ∈ (orbit P x)ᶜ, ∀ g ∈ P, g y = y := by
      intro y hy g hg
      have hy1 : (orbit P y).ncard = 1 := by
        by_contra hne
        have hyp : (orbit P y).ncard = p := (hsize y).resolve_left hne
        have hsub : orbit P y ⊆ (orbit P x)ᶜ := by
          rintro v hv hvO
          obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup_iff.mp hv
          have h1 := (hOinv k⁻¹ (inv_mem hk) (k y)).mp hvO
          have h2 : k⁻¹ (k y) = y := by simp
          rw [h2] at h1
          exact hy h1
        have heq : orbit P y = (orbit P x)ᶜ :=
          Set.eq_of_subset_of_ncard_le hsub (le_of_eq (by rw [hyp, hCcard])) (Set.toFinite _)
        have hzy : z ∈ orbit P y := by
          rw [heq]
          exact hzO
        have hzz : orbit P z = orbit P y := MulAction.orbit_eq_iff.mpr hzy
        rw [hzz, hyp] at hz
        omega
      obtain ⟨b, hb⟩ := Set.ncard_eq_one.mp hy1
      have h1 : g y ∈ orbit P y := mem_orbit_subgroup_iff.mpr ⟨g, hg, rfl⟩
      have h2 : y ∈ orbit P y := mem_orbit_self y
      rw [hb, Set.mem_singleton_iff] at h1 h2
      rw [h1, h2]
    classical
    have hle : P ≤ (Equiv.Perm.ofSubtype (p := (· ∈ orbit P x))).range := by
      intro g hg
      refine ⟨g.subtypePerm (fun v => (hOinv g hg v).symm), ?_⟩
      apply Equiv.Perm.ofSubtype_subtypePerm
      intro v hv
      by_contra hvO
      exact hv (hCfix v hvO g hg)
    have hinj : Function.Injective (Equiv.Perm.ofSubtype (p := (· ∈ orbit P x))) :=
      Equiv.Perm.ofSubtype_injective
    have hdvd : Nat.card P ∣
        Nat.card (Equiv.Perm.ofSubtype (p := (· ∈ orbit P x))).range :=
      Subgroup.card_dvd_of_le hle
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_perm,
      Nat.card_coe_set_eq, hxp] at hdvd
    exact not_sq_dvd_factorial hp.out (hPp.trans hdvd)
  exact (hsize u).resolve_left (hnofix u)

end Orbits

section Core

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem stabilizer_normal {p : ℕ} [hp : Fact p.Prime] {P : Subgroup (Perm Ω)} (hP : IsPGroup p P)
    (hPp : p ^ 2 ∣ Nat.card P) (hpz : ∀ z : Ω, (orbit P z).ncard = p) (z : Ω) :
    (stabilizer P z).Normal := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hP
  have ha1 : a ≠ 0 := by
    rintro rfl
    rw [ha, pow_zero] at hPp
    have := Nat.le_of_dvd one_pos hPp
    nlinarith [hp.out.two_le]
  apply Subgroup.normal_of_index_eq_minFac_card
  rw [index_stabilizer, hpz, ha, minFac_pow_eq hp.out ha1]

theorem two_block_absurd {p : ℕ} [hp : Fact p.Prime] {P W : Subgroup (Perm Ω)}
    (hPp : p ^ 2 ∣ Nat.card P) {z z' : Ω} (hne : z' ≠ z)
    (hpz : (orbit P z).ncard = p) (hsn : (stabilizer P z).Normal)
    (hnorm : ∀ g ∈ P, ∀ w ∈ W, g * w * g⁻¹ ∈ W)
    (hWz : orbit W z = {z, z'}) (hcov : ∀ u : Ω, ∃ g ∈ P ⊔ W, g z = u) : False := by
  have hWmem : ∀ w ∈ W, w z = z ∨ w z = z' := by
    intro w hw
    have h : w z ∈ orbit W z := mem_orbit_subgroup_iff.mpr ⟨w, hw, rfl⟩
    rw [hWz] at h
    simpa using h
  have hz'orb : z' ∈ orbit W z := by
    rw [hWz]
    simp
  have hWz'eq : orbit W z' = orbit W z := MulAction.orbit_eq_iff.mpr hz'orb
  have hWmem' : ∀ w ∈ W, w z' = z ∨ w z' = z' := by
    intro w hw
    have h : w z' ∈ orbit W z' := mem_orbit_subgroup_iff.mpr ⟨w, hw, rfl⟩
    rw [hWz'eq, hWz] at h
    simpa using h
  obtain ⟨w₀, hw₀, hw₀z⟩ := mem_orbit_subgroup_iff.mp hz'orb
  have key_a : ∀ g ∈ P, g z = z → g z' = z' := by
    intro g hg hgz
    have hgi : g⁻¹ z = z := by
      calc g⁻¹ z = g⁻¹ (g z) := by rw [hgz]
        _ = z := by simp
    have hk := hnorm g hg w₀ hw₀
    have hkz : (g * w₀ * g⁻¹) z = g z' := by
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hgi, hw₀z]
    rcases hWmem _ hk with h | h
    · rw [hkz] at h
      exfalso
      apply hne
      apply g.injective
      rw [h, hgz]
    · rwa [hkz] at h
  obtain ⟨Q, hQ⟩ : ∃ Q : Set Ω, Q = orbit P z ∪ orbit P z' := ⟨_, rfl⟩
  have hmemQ : ∀ v, v ∈ Q ↔ (v ∈ orbit P z ∨ v ∈ orbit P z') := fun v => by
    rw [hQ]
    exact Iff.rfl
  have hPQ : ∀ g ∈ P, ∀ v, v ∈ Q → g v ∈ Q := by
    intro g hg v hv
    rcases (hmemQ v).mp hv with hv | hv
    · obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup_iff.mp hv
      exact (hmemQ _).mpr (Or.inl (mem_orbit_subgroup_iff.mpr
        ⟨g * h, mul_mem hg hh, by rw [Equiv.Perm.mul_apply]⟩))
    · obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup_iff.mp hv
      exact (hmemQ _).mpr (Or.inr (mem_orbit_subgroup_iff.mpr
        ⟨g * h, mul_mem hg hh, by rw [Equiv.Perm.mul_apply]⟩))
  have hWQ : ∀ w ∈ W, ∀ v, v ∈ Q → w v ∈ Q := by
    intro w hw v hv
    have hwc : ∀ h ∈ P, h⁻¹ * w * h ∈ W := by
      intro h hh
      have := hnorm h⁻¹ (inv_mem hh) w hw
      simpa [mul_assoc] using this
    apply (hmemQ _).mpr
    rcases (hmemQ v).mp hv with hv | hv
    · obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup_iff.mp hv
      have hk := hwc h hh
      have hw' : w (h z) = h ((h⁻¹ * w * h) z) := by simp
      rw [hw']
      rcases hWmem _ hk with h1 | h1
      · rw [h1]
        exact Or.inl (mem_orbit_subgroup_iff.mpr ⟨h, hh, rfl⟩)
      · rw [h1]
        exact Or.inr (mem_orbit_subgroup_iff.mpr ⟨h, hh, rfl⟩)
    · obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup_iff.mp hv
      have hk := hwc h hh
      have hw' : w (h z') = h ((h⁻¹ * w * h) z') := by simp
      rw [hw']
      rcases hWmem' _ hk with h1 | h1
      · rw [h1]
        exact Or.inl (mem_orbit_subgroup_iff.mpr ⟨h, hh, rfl⟩)
      · rw [h1]
        exact Or.inr (mem_orbit_subgroup_iff.mpr ⟨h, hh, rfl⟩)
  have hsetQ : ∀ g : Perm Ω, (∀ v, v ∈ Q → g v ∈ Q) → (∀ v, v ∈ Q → g⁻¹ v ∈ Q) → g • Q = Q := by
    intro g h1 h2
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact h1 y hy
    · intro hv
      exact ⟨g⁻¹ v, h2 v hv, by simp [Equiv.Perm.smul_def]⟩
  have hPstab : ∀ g ∈ P, g • Q = Q := fun g hg =>
    hsetQ g (fun v hv => hPQ g hg v hv) (fun v hv => hPQ g⁻¹ (inv_mem hg) v hv)
  have hWstab : ∀ w ∈ W, w • Q = Q := fun w hw =>
    hsetQ w (fun v hv => hWQ w hw v hv) (fun v hv => hWQ w⁻¹ (inv_mem hw) v hv)
  have hstab : P ⊔ W ≤ stabilizer (Perm Ω) Q :=
    sup_le (fun g hg => mem_stabilizer_iff.mpr (hPstab g hg))
      (fun w hw => mem_stabilizer_iff.mpr (hWstab w hw))
  have hallQ : ∀ u : Ω, u ∈ Q := by
    intro u
    obtain ⟨g, hg, rfl⟩ := hcov u
    have hgQ : g • Q = Q := mem_stabilizer_iff.mp (hstab hg)
    have hzQ : z ∈ Q := (hmemQ z).mpr (Or.inl (mem_orbit_subgroup_iff.mpr ⟨1, one_mem _, rfl⟩))
    rw [← hgQ]
    exact Set.smul_mem_smul_set hzQ
  have hfix : ∀ h ∈ P, h z = z → h = 1 := by
    intro h hh hhz
    have hc : ∀ g ∈ P, (g⁻¹ * h * g) z = z := by
      intro g hg
      have hmem : (⟨h, hh⟩ : ↥P) ∈ stabilizer P z := mem_stabilizer_iff.mpr hhz
      have hc' := hsn.conj_mem _ hmem ⟨g⁻¹, inv_mem hg⟩
      rw [mem_stabilizer_iff] at hc'
      have hc'' : (g⁻¹ * h * g⁻¹⁻¹) z = z := hc'
      rwa [inv_inv] at hc''
    apply Equiv.ext
    intro u
    rcases (hmemQ u).mp (hallQ u) with hu | hu
    · obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.mp hu
      rw [Equiv.Perm.one_apply]
      calc h (g z) = g ((g⁻¹ * h * g) z) := by simp
        _ = g z := by rw [hc g hg]
    · obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.mp hu
      rw [Equiv.Perm.one_apply]
      have hgg : g⁻¹ * h * g ∈ P := mul_mem (mul_mem (inv_mem hg) hh) hg
      calc h (g z') = g ((g⁻¹ * h * g) z') := by simp
        _ = g z' := by rw [key_a _ hgg (hc g hg)]
  have hbot : stabilizer P z = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    rw [mem_stabilizer_iff] at hs
    apply Subtype.ext
    exact hfix s.1 s.2 hs
  have hcard := Subgroup.index_mul_card (H := stabilizer P z)
  rw [index_stabilizer, hpz, hbot, Subgroup.card_bot, mul_one] at hcard
  rw [← hcard] at hPp
  have := Nat.le_of_dvd hp.out.pos hPp
  nlinarith [hp.out.two_le]

theorem core {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (hΩ : Nat.card Ω = 2 * p)
    {P W : Subgroup (Perm Ω)} (hP : IsPGroup p P) (hPp : p ^ 2 ∣ Nat.card P)
    (hW : Nat.Coprime p (Nat.card W)) (hnorm : ∀ g ∈ P, ∀ w ∈ W, g * w * g⁻¹ ∈ W) :
    W = ⊥ := by
  have hpz : ∀ u : Ω, (orbit P u).ncard = p := fun u => ncard_orbit_eq_p hp5 hΩ hP hPp u
  have hWfix : ∀ z : Ω, (orbit W z).ncard = 1 := by
    intro z
    have hmW : (orbit W z).ncard ∣ Nat.card W := by
      rw [← index_stabilizer]
      exact Subgroup.index_dvd_card _
    have hpm : ¬ p ∣ (orbit W z).ncard := fun h =>
      (Nat.Prime.coprime_iff_not_dvd hp.out).mp hW (h.trans hmW)
    have hmcop : Nat.Coprime (orbit W z).ncard p :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpm).symm
    have hmpos : 0 < (orbit W z).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨z, mem_orbit_self z⟩
    have hGW : ∀ g ∈ P ⊔ W, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
      have hle : P ⊔ W ≤ normalizer W :=
        sup_le (fun g hg => mem_normalizer_iff.mpr fun w => ⟨fun hw => hnorm g hg w hw,
          fun hw => by
            have := hnorm g⁻¹ (inv_mem hg) _ hw
            simpa [mul_assoc] using this⟩) le_normalizer
      intro g hg w hw
      exact (mem_normalizer_iff.mp (hle hg) w).mp hw
    have hNn : (W.subgroupOf (P ⊔ W)).Normal := by
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := hGW _ g.2 _ hn
      simpa using this
    have hIL := ncard_orbit_normal_dvd (G := ↥(P ⊔ W)) (X := Ω) (W.subgroupOf (P ⊔ W)) z
    rw [orbit_subgroupOf_eq le_sup_right z] at hIL
    have hGcase : orbit ↥(P ⊔ W) z = orbit P z ∨ orbit ↥(P ⊔ W) z = Set.univ := by
      by_cases hsub : ∀ u ∈ orbit ↥(P ⊔ W) z, u ∈ orbit P z
      · left
        apply Set.Subset.antisymm hsub
        intro u hu
        obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.mp hu
        exact mem_orbit_subgroup_iff.mpr ⟨g, Subgroup.mem_sup_left hg, rfl⟩
      · right
        push_neg at hsub
        obtain ⟨u, huG, huP⟩ := hsub
        have hcompl : (orbit P z)ᶜ.ncard = p := by
          have h := Set.ncard_add_ncard_compl (orbit P z)
          rw [hΩ, hpz z] at h
          omega
        have hPu_sub : orbit P u ⊆ (orbit P z)ᶜ := by
          intro v hv
          rw [Set.mem_compl_iff]
          intro hvz
          obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.mp hv
          apply huP
          obtain ⟨h, hh, hhz⟩ := mem_orbit_subgroup_iff.mp hvz
          refine mem_orbit_subgroup_iff.mpr ⟨g⁻¹ * h, mul_mem (inv_mem hg) hh, ?_⟩
          rw [Equiv.Perm.mul_apply, hhz]
          simp
        have hPu_eq : orbit P u = (orbit P z)ᶜ :=
          Set.eq_of_subset_of_ncard_le hPu_sub (le_of_eq (by rw [hcompl, hpz u])) (Set.toFinite _)
        have hPz_sub : orbit P z ⊆ orbit ↥(P ⊔ W) z := by
          intro v hv
          obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.mp hv
          exact mem_orbit_subgroup_iff.mpr ⟨g, Subgroup.mem_sup_left hg, rfl⟩
        have hPu_G : orbit P u ⊆ orbit ↥(P ⊔ W) z := by
          intro v hv
          obtain ⟨g, hg, rfl⟩ := mem_orbit_subgroup_iff.mp hv
          obtain ⟨h, hh, rfl⟩ := mem_orbit_subgroup_iff.mp huG
          exact mem_orbit_subgroup_iff.mpr
            ⟨g * h, mul_mem (Subgroup.mem_sup_left hg) hh, by rw [Equiv.Perm.mul_apply]⟩
        apply Set.eq_univ_of_forall
        intro v
        by_cases hv : v ∈ orbit P z
        · exact hPz_sub hv
        · apply hPu_G
          rw [hPu_eq]
          exact hv
    rcases hGcase with hGP | hGU
    · rw [hGP, hpz z] at hIL
      rcases (Nat.dvd_prime hp.out).mp hIL with h1 | h1
      · exact h1
      · exact absurd (by rw [h1]) hpm
    · rw [hGU, Set.ncard_univ, hΩ] at hIL
      have h2 : (orbit W z).ncard ∣ 2 := hmcop.dvd_of_dvd_mul_right hIL
      have h3 : (orbit W z).ncard ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      rcases (by omega : (orbit W z).ncard = 1 ∨ (orbit W z).ncard = 2) with h1 | h1
      · exact h1
      · exfalso
        obtain ⟨a, b, hab, hWab⟩ := Set.ncard_eq_two.mp h1
        have hzmem : z ∈ orbit W z := mem_orbit_self z
        rw [hWab] at hzmem
        have hcov : ∀ u : Ω, ∃ g ∈ P ⊔ W, g z = u := fun u => by
          have hu : u ∈ orbit ↥(P ⊔ W) z := by
            rw [hGU]
            exact Set.mem_univ u
          exact mem_orbit_subgroup_iff.mp hu
        rcases hzmem with h | h
        · exact two_block_absurd hPp (z' := b) (fun e => hab (h.symm.trans e.symm))
            (hpz z) (stabilizer_normal hP hPp hpz z) hnorm (by rw [hWab, h]) hcov
        · have hzb : z = b := Set.mem_singleton_iff.mp h
          exact two_block_absurd hPp (z' := a) (fun e => hab (e.trans hzb))
            (hpz z) (stabilizer_normal hP hPp hpz z) hnorm (by rw [hWab, hzb, Set.pair_comm]) hcov
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  apply Equiv.ext
  intro z
  obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp (hWfix z)
  have h1 : w z ∈ orbit W z := mem_orbit_subgroup_iff.mpr ⟨w, hw, rfl⟩
  have h2 : z ∈ orbit W z := mem_orbit_self z
  rw [ha, Set.mem_singleton_iff] at h1 h2
  rw [Equiv.Perm.one_apply, h1, h2]

end Core

end AltCore

theorem signalizerTrivialAlt_holds : SignalizerTrivialAlt := by
  intro p hp hp5 K _ _ hK P W hW hnorm
  obtain ⟨e⟩ := hK
  haveI : Fact p.Prime := ⟨hp⟩
  have hn : 7 ≤ 2 * p := by omega
  haveI : Nontrivial (Fin (2 * p)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hA : 2 * Nat.card (alternatingGroup (Fin (2 * p))) = (2 * p).factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  have hdvdF : p ^ 2 ∣ (2 * p).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : 2 * p ≠ 0), sq]
    exact mul_dvd_mul (dvd_mul_left p 2) (Nat.dvd_factorial hp.pos (by omega))
  have hodd : Nat.Coprime (p ^ 2) 2 :=
    Nat.Coprime.pow_left 2 ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
  have hKdvd : p ^ 2 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    apply hodd.dvd_of_dvd_mul_left
    rw [hA]
    exact hdvdF
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hfac : 2 ≤ (Nat.card K).factorization p :=
    (hp.pow_dvd_iff_le_factorization hK0).mp hKdvd
  have hPcard : p ^ 2 ∣ Nat.card (P : Subgroup K) := by
    rw [Sylow.card_eq_multiplicity P]
    exact pow_dvd_pow p hfac
  have hPgroup : IsPGroup p (P : Subgroup K) := P.isPGroup'
  set θ : MulAut K →* Perm (Fin (2 * p)) := (altAutEquiv hn e).toMonoidHom with hθ
  set ψ : K →* Perm (Fin (2 * p)) := psiAlt e with hψ
  have hθinj : Function.Injective θ := (altAutEquiv hn e).injective
  have hψinj : Function.Injective ψ := psiAlt_injective e
  have hθk : ∀ k : K, θ (MulAut.conj k) = ψ k := fun k => altAutEquiv_conj hn e k
  set Wp : Subgroup (Perm (Fin (2 * p))) := W.map θ with hWp
  set Pp : Subgroup (Perm (Fin (2 * p))) := (P : Subgroup K).map ψ with hPp'
  have hWp_card : Nat.card Wp = Nat.card W := Subgroup.card_map_of_injective hθinj
  have hPp_card : Nat.card Pp = Nat.card (P : Subgroup K) :=
    Subgroup.card_map_of_injective hψinj
  have hPp_pgroup : IsPGroup p Pp := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPgroup
    exact IsPGroup.iff_card.mpr ⟨k, by rw [hPp_card, hk]⟩
  have hnorm' : ∀ g ∈ Pp, ∀ x ∈ Wp, g * x * g⁻¹ ∈ Wp := by
    intro g hg x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hx
    have heq : ψ k * θ w₀ * (ψ k)⁻¹ = θ (MulAut.conj k * w₀ * (MulAut.conj k)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hθk]
    rw [heq]
    exact Subgroup.mem_map_of_mem θ (hnorm k hk w₀ hw₀)
  have hWp_bot : Wp = ⊥ :=
    AltCore.core (Ω := Fin (2 * p)) hp5 (by simp) hPp_pgroup
      (by rw [hPp_card]; exact hPcard) (by rw [hWp_card]; exact hW) hnorm'
  rw [Subgroup.eq_bot_iff_forall]
  intro w hw
  have hθw : θ w ∈ Wp := Subgroup.mem_map_of_mem θ hw
  rw [hWp_bot, Subgroup.mem_bot] at hθw
  exact hθinj (by rw [hθw, map_one])


end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

end
