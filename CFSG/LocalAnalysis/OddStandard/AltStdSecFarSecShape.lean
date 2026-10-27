module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarSecCore
public import CFSG.LocalAnalysis.OddStandard.AltStdSecHerQuot

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm

section Quot

variable {G : Type*} [Group G]

abbrev secPin (P : Subgroup G) : Subgroup ↥(centralizer (P : Set G)) :=
  P.subgroupOf (centralizer (P : Set G))

instance normal_secPin (P : Subgroup G) : (secPin P).Normal where
  conj_mem := by
    intro p hp y
    have hp' : (p : G) ∈ P := hp
    have hc : (p : G) * y = y * p := mem_centralizer_iff.1 y.2 p hp'
    show ((y * p * y⁻¹ : ↥(centralizer (P : Set G))) : G) ∈ P
    have : (y : G) * p * (y : G)⁻¹ = p := by rw [← hc]; group
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, this]
    exact hp'

abbrev secQ (P : Subgroup G) : Type _ := ↥(centralizer (P : Set G)) ⧸ secPin P

theorem mk_eq_one_iff {P : Subgroup G} {y : ↥(centralizer (P : Set G))} :
    (QuotientGroup.mk y : secQ P) = 1 ↔ (y : G) ∈ P :=
  QuotientGroup.eq_one_iff y

end Quot

@[expose] def fourTail (m : ℕ) : Finset (Fin (m + 3)) :=
  Finset.univ.filter fun i => 4 ≤ (i : ℕ) ∧ (i : ℕ) < m + 1

theorem mem_fourTail {m : ℕ} {i : Fin (m + 3)} : i ∈ fourTail m ↔ 4 ≤ (i : ℕ) ∧ (i : ℕ) < m + 1 := by
  simp [fourTail]

theorem card_fourTail (m : ℕ) (hm : 3 ≤ m) : (fourTail m).card = m - 3 := by
  have : fourTail m = ((Finset.range (m + 1)).filter (fun i => 4 ≤ i)).attachFin
      (fun i hi => by simp at hi; omega) := by
    ext i; simp [fourTail]; omega
  rw [this, Finset.card_attachFin]
  have h2 : (Finset.range (m + 1)).filter (fun i => 4 ≤ i) = Finset.Ico 4 (m + 1) := by
    ext i; simp; omega
  rw [h2, Nat.card_Ico]
  omega

section Shape

variable {G : Type*} [Group G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

include hR in
theorem fixSub_comm_secP {s : Perm (Fin (m + 3))} (hs : s ∈ fixSub (fourSet (m + 3))) :
    O.φ s ∈ centralizer (secP O R : Set G) := by
  rw [mem_centralizer_iff]
  rintro _ ⟨r, hr, rfl⟩
  rw [O.φ_comm_iff]
  exact hR.comm_fixSub hr hs

include hR in
theorem z_mem_secY : z ∈ centralizer (secP O R : Set G) := by
  have h := fixSub_comm_secP O hR hR.tau_mem_fixSub
  rwa [O.φ_tau] at h

theorem fourTail_subset_compl : fourTail m ⊆ (fourSet (m + 3))ᶜ := by
  intro i hi
  rw [mem_fourTail] at hi
  simp [mem_fourSet]; omega

theorem altSub_fourTail_le : altSub (fourTail m) ≤ fixSub (fourSet (m + 3)) := by
  intro σ hσ i hi
  exact (mem_altSub.1 hσ).2 i (fun h => by
    have := fourTail_subset_compl h
    simp at this; exact this hi)

@[expose] noncomputable def secT : secQ (secP O R) :=
  QuotientGroup.mk ⟨z, z_mem_secY O hR⟩

@[expose] noncomputable def secIncl (K : Subgroup (Perm (Fin (m + 3))))
    (hK : K ≤ fixSub (fourSet (m + 3))) : K →* secQ (secP O R) :=
  (QuotientGroup.mk' _).comp
    ((O.φ.comp K.subtype).codRestrict _ (fun σ => fixSub_comm_secP O hR (hK σ.2)))

theorem secIncl_apply (K : Subgroup (Perm (Fin (m + 3)))) (hK : K ≤ fixSub (fourSet (m + 3)))
    (σ : K) : secIncl O hR K hK σ = QuotientGroup.mk ⟨O.φ σ, fixSub_comm_secP O hR (hK σ.2)⟩ :=
  rfl

@[expose] noncomputable def secPsi : altSub (fourTail m) →* secQ (secP O R) :=
  secIncl O hR _ altSub_fourTail_le

theorem secPsi_apply (σ : altSub (fourTail m)) :
    secPsi O hR σ = QuotientGroup.mk ⟨O.φ σ, fixSub_comm_secP O hR (altSub_fourTail_le σ.2)⟩ :=
  rfl

include hR in
theorem eq_one_of_mem_R_of_mem_fixSub {r : Perm (Fin (m + 3))} (hr : r ∈ R)
    (hrF : r ∈ fixSub (fourSet (m + 3))) : r = 1 := by
  refine Equiv.ext fun i => ?_
  by_cases hi : i ∈ fourSet (m + 3)
  · exact hrF i hi
  · exact hR.le hr i (by simpa using hi)

include hR in
theorem eq_one_of_φ_mem_secP {s : Perm (Fin (m + 3))} (hs : s ∈ fixSub (fourSet (m + 3)))
    (hsP : O.φ s ∈ secP O R) : s = 1 := by
  obtain ⟨r, hr, hrs⟩ := hsP
  have := O.φ_injective hrs
  subst this
  exact eq_one_of_mem_R_of_mem_fixSub hR hr hs

theorem secIncl_injective (K : Subgroup (Perm (Fin (m + 3))))
    (hK : K ≤ fixSub (fourSet (m + 3))) : Function.Injective (secIncl O hR K hK) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  rw [secIncl_apply, mk_eq_one_iff] at hσ
  exact Subtype.ext (eq_one_of_φ_mem_secP O hR (hK σ.2) hσ)

theorem secPsi_injective : Function.Injective (secPsi O hR) :=
  secIncl_injective O hR _ _

@[expose] noncomputable def secB : Subgroup (secQ (secP O R)) := (secPsi O hR).range

@[expose] noncomputable def secBEquiv : secB O hR ≃* alternatingGroup (Fin (m - 3)) :=
  (MonoidHom.ofInjective (secPsi_injective O hR)).symm.trans
    ((altSubEquiv (fourTail m)).trans
      (Equiv.altCongrHom (finCongr (card_fourTail m hR.three_le))))

theorem secT_mul_self : secT O hR * secT O hR = 1 := by
  rw [secT, ← QuotientGroup.mk_mul]
  have : (⟨z, z_mem_secY O hR⟩ * ⟨z, z_mem_secY O hR⟩ : ↥(centralizer (secP O R : Set G))) = 1 :=
    Subtype.ext O.D.sq
  rw [this, QuotientGroup.mk_one]

theorem secT_ne_one : secT O hR ≠ 1 := by
  intro h
  rw [secT, mk_eq_one_iff] at h
  obtain ⟨r, hr, hrz⟩ := h
  have hrτ := O.φ_injective (hrz.trans O.φ_tau.symm)
  subst hrτ
  have h1 := eq_one_of_mem_R_of_mem_fixSub hR hr hR.tau_mem_fixSub
  have h2 := DFunLike.congr_fun h1 ⟨m + 1, by omega⟩
  simp [OverData.tau] at h2

theorem orderOf_secT : orderOf (secT O hR) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact secT_mul_self O hR) (secT_ne_one O hR)

end Shape

section Tail

variable {m : ℕ}

theorem tail_of_comm_tau {s : Perm (Fin (m + 3))} (hsτ : s * OverData.tau m = OverData.tau m * s)
    {i : Fin (m + 3)} (hi : m + 1 ≤ (i : ℕ)) : m + 1 ≤ (s i : ℕ) := by
  have hne : OverData.tau m i ≠ i := by
    rw [OverData.tau, swap_apply_ne_self_iff]
    refine ⟨by simp [Fin.ext_iff], ?_⟩
    rcases (by omega : (i : ℕ) = m + 1 ∨ (i : ℕ) = m + 2) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  have h1 : OverData.tau m (s i) ≠ s i := by
    intro h
    apply hne
    apply s.injective
    have := DFunLike.congr_fun hsτ i
    simp only [Perm.mul_apply] at this
    rw [this, h]
  rw [OverData.tau, swap_apply_ne_self_iff] at h1
  rcases h1.2 with h | h
  · rw [h]
  · rw [h]; simp

theorem comm_tau_inv {s : Perm (Fin (m + 3))} (hsτ : s * OverData.tau m = OverData.tau m * s) :
    s⁻¹ * OverData.tau m = OverData.tau m * s⁻¹ := by
  calc s⁻¹ * OverData.tau m = s⁻¹ * (OverData.tau m * s) * s⁻¹ := by group
    _ = s⁻¹ * (s * OverData.tau m) * s⁻¹ := by rw [hsτ]
    _ = OverData.tau m * s⁻¹ := by group

theorem mem_fourTail_of_comm_tau {s : Perm (Fin (m + 3))} (hs : s ∈ fixSub (fourSet (m + 3)))
    (hsτ : s * OverData.tau m = OverData.tau m * s) {i : Fin (m + 3)} (hi : i ∈ fourTail m) :
    s i ∈ fourTail m := by
  rw [mem_fourTail] at hi ⊢
  constructor
  · by_contra h
    have h' : (s i : ℕ) < 4 := by omega
    have h1 : s (s i) = s i := hs (s i) (by rw [mem_fourSet]; exact h')
    have := s.injective h1
    rw [this] at h'
    omega
  · by_contra h
    have := tail_of_comm_tau (comm_tau_inv hsτ) (i := s i) (by omega)
    have h2 : s⁻¹ (s i) = i := by simp
    rw [h2] at this
    omega

theorem mem_fourTail_iff_of_comm_tau {s : Perm (Fin (m + 3))} (hs : s ∈ fixSub (fourSet (m + 3)))
    (hsτ : s * OverData.tau m = OverData.tau m * s) (i : Fin (m + 3)) :
    i ∈ fourTail m ↔ s i ∈ fourTail m := by
  refine ⟨mem_fourTail_of_comm_tau hs hsτ, fun h => ?_⟩
  have := mem_fourTail_of_comm_tau (inv_mem hs) (comm_tau_inv hsτ) h
  have h2 : s⁻¹ (s i) = i := by simp
  rwa [h2] at this

theorem eq_one_or_eq_tau {s : Perm (Fin (m + 3))} (hs : ∀ i : Fin (m + 3), (i : ℕ) < m + 1 → s i = i) :
    s = 1 ∨ s = OverData.tau m := by
  refine eq_one_or_eq_of_fixes_compl (p := ⟨m + 1, by omega⟩) (q := ⟨m + 2, by omega⟩)
    (by simp [Fin.ext_iff]) (fun x hx1 hx2 => hs x ?_)
  have h1 : (x : ℕ) ≠ m + 1 := fun h => hx1 (Fin.ext h)
  have h2 : (x : ℕ) ≠ m + 2 := fun h => hx2 (Fin.ext h)
  omega

end Tail

section ShapeHyp

variable {G : Type*} [Group G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

include hR in
theorem φ_conj_eq {r s σ : Perm (Fin (m + 3))} (hr : r ∈ R) (hs : s ∈ fixSub (fourSet (m + 3)))
    (hσ : σ ∈ fixSub (fourSet (m + 3))) :
    O.φ r * O.φ s * O.φ σ * (O.φ r * O.φ s)⁻¹ = O.φ (s * σ * s⁻¹) := by
  have hc : r * (s * σ * s⁻¹) = (s * σ * s⁻¹) * r :=
    hR.comm_fixSub hr (mul_mem (mul_mem hs hσ) (inv_mem hs))
  rw [← map_mul, ← map_mul, ← map_inv, ← map_mul]
  congr 1
  calc r * s * σ * (r * s)⁻¹ = r * (s * σ * s⁻¹) * r⁻¹ := by group
    _ = (s * σ * s⁻¹) * r * r⁻¹ := by rw [hc]
    _ = s * σ * s⁻¹ := by group

include hR in
theorem comm_z_of_comm_secT (hm : 10 ≤ m) (h : ↥(centralizer (secP O R : Set G)))
    (hc : (QuotientGroup.mk h : secQ (secP O R)) * secT O hR = secT O hR * QuotientGroup.mk h) :
    (h : G) * z = z * h := by
  set zz : ↥(centralizer (secP O R : Set G)) := ⟨z, z_mem_secY O hR⟩ with hzz
  have h1 : (QuotientGroup.mk zz : secQ (secP O R)) = QuotientGroup.mk (h * zz * h⁻¹) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    change secT O hR = QuotientGroup.mk h * secT O hR * (QuotientGroup.mk h)⁻¹
    rw [hc]
    group
  have h2 := QuotientGroup.eq.1 h1
  have hp : z⁻¹ * ((h : G) * z * (h : G)⁻¹) ∈ secP O R := h2
  have hc' : IsConj z (z * (z⁻¹ * ((h : G) * z * (h : G)⁻¹))) := by
    rw [mul_inv_cancel_left]
    exact isConj_iff.2 ⟨h, rfl⟩
  have h3 := eq_one_of_isConj_z_mul O hR hm hp hc'
  have h4 : (h : G) * z * (h : G)⁻¹ = z := by
    calc (h : G) * z * (h : G)⁻¹ = z * (z⁻¹ * ((h : G) * z * (h : G)⁻¹)) := by group
      _ = z := by rw [h3, mul_one]
  calc (h : G) * z = (h : G) * z * (h : G)⁻¹ * h := by group
    _ = z * h := by rw [h4]

include hR in
theorem secB_le_cent : secB O hR ≤ centralizer ({secT O hR} : Set (secQ (secP O R))) := by
  rintro _ ⟨σ, rfl⟩
  rw [mem_centralizer_singleton_iff, secPsi_apply, secT, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1
  apply Subtype.ext
  change O.φ σ * z = z * O.φ σ
  have h1 : (σ : Perm (Fin (m + 3))) ⟨m + 1, by omega⟩ = ⟨m + 1, by omega⟩ :=
    (mem_altSub.1 σ.2).2 _ (by rw [mem_fourTail]; simp)
  have h2 : (σ : Perm (Fin (m + 3))) ⟨m + 2, by omega⟩ = ⟨m + 2, by omega⟩ :=
    (mem_altSub.1 σ.2).2 _ (by rw [mem_fourTail]; simp)
  have key := (O.φ_comm_iff (x := (σ : Perm (Fin (m + 3)))) (y := OverData.tau m)).2
    (swap_comm_of_fixed h1 h2).symm
  rwa [O.φ_tau] at key

include hR in
theorem cent_secT_le_normalizer (hm : 10 ≤ m) :
    centralizer ({secT O hR} : Set (secQ (secP O R))) ≤
      normalizer (secB O hR : Set (secQ (secP O R))) := by
  have key : ∀ q ∈ centralizer ({secT O hR} : Set (secQ (secP O R))), ∀ b ∈ secB O hR,
      q * b * q⁻¹ ∈ secB O hR := by
    intro q hq b hb
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    have hhz := comm_z_of_comm_secT O hR hm h (mem_centralizer_singleton_iff.1 hq)
    obtain ⟨r, hr, s, hs, hsτ, hrs⟩ := exists_of_cent_z O hR h.2 hhz
    obtain ⟨σ, rfl⟩ := hb
    have hN := mem_normalizer_altSub (fun i => mem_fourTail_iff_of_comm_tau hs hsτ i)
    have hσ' : s * σ * s⁻¹ ∈ altSub (fourTail m) := (mem_normalizer_iff.1 hN σ).1 σ.2
    refine ⟨⟨s * σ * s⁻¹, hσ'⟩, ?_⟩
    rw [secPsi_apply, secPsi_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    change O.φ (s * σ * s⁻¹) = (h : G) * O.φ σ * (h : G)⁻¹
    rw [hrs, φ_conj_eq O hR hr hs (altSub_fourTail_le σ.2)]
  intro q hq
  rw [mem_normalizer_iff]
  intro b
  refine ⟨key q hq b, fun hb => ?_⟩
  have := key q⁻¹ (inv_mem hq) _ hb
  have e : q⁻¹ * (q * b * q⁻¹) * q⁻¹⁻¹ = b := by group
  rwa [e] at this

include hR in
theorem cent_secB_inf_le (hm : 10 ≤ m) :
    centralizer (secB O hR : Set (secQ (secP O R))) ⊓
        centralizer ({secT O hR} : Set (secQ (secP O R))) ≤ zpowers (secT O hR) := by
  rintro q ⟨hqB, hqt⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hhz := comm_z_of_comm_secT O hR hm h (mem_centralizer_singleton_iff.1 hqt)
  obtain ⟨r, hr, s, hs, hsτ, hrs⟩ := exists_of_cent_z O hR h.2 hhz
  have hsc : s ∈ centralizer ((altSub (fourTail m) : Subgroup (Perm (Fin (m + 3)))) :
      Set (Perm (Fin (m + 3)))) := by
    rw [mem_centralizer_iff]
    intro σ hσ
    have h1 := mem_centralizer_iff.1 hqB (secPsi O hR ⟨σ, hσ⟩) ⟨⟨σ, hσ⟩, rfl⟩
    have hσF : σ ∈ fixSub (fourSet (m + 3)) := altSub_fourTail_le hσ
    set σ' : ↥(centralizer (secP O R : Set G)) :=
      ⟨O.φ σ, fixSub_comm_secP O hR hσF⟩ with hσ'
    have h2 : (QuotientGroup.mk (h * σ' * h⁻¹ * σ'⁻¹) : secQ (secP O R)) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
        QuotientGroup.mk_inv]
      have h1' : (QuotientGroup.mk σ' : secQ (secP O R)) * QuotientGroup.mk h =
          QuotientGroup.mk h * QuotientGroup.mk σ' := h1
      rw [← h1']
      group
    rw [mk_eq_one_iff] at h2
    have h3 : ((h * σ' * h⁻¹ * σ'⁻¹ : ↥(centralizer (secP O R : Set G))) : G) =
        O.φ (s * σ * s⁻¹ * σ⁻¹) := by
      change (h : G) * O.φ σ * (h : G)⁻¹ * (O.φ σ)⁻¹ = _
      rw [hrs, φ_conj_eq O hR hr hs hσF, map_mul _ (s * σ * s⁻¹), map_inv]
    rw [h3] at h2
    have h4 := eq_one_of_φ_mem_secP O hR (mul_mem (mul_mem (mul_mem hs hσF) (inv_mem hs))
      (inv_mem hσF)) h2
    calc σ * s = (s * σ * s⁻¹ * σ⁻¹)⁻¹ * s * σ := by group
      _ = s * σ := by rw [h4, inv_one, one_mul]
  have hcard : 4 ≤ (fourTail m).card := by rw [card_fourTail m hR.three_le]; omega
  have hfix := (mem_centralizer_altSub_iff hcard).1 hsc
  have hs1 : s = 1 ∨ s = OverData.tau m := by
    refine eq_one_or_eq_tau (fun i hi => ?_)
    by_cases h4 : (i : ℕ) < 4
    · exact hs i (by rw [mem_fourSet]; exact h4)
    · exact hfix i (by rw [mem_fourTail]; omega)
  have hφs : O.φ s ∈ centralizer (secP O R : Set G) := fixSub_comm_secP O hR hs
  have hmk : (QuotientGroup.mk h : secQ (secP O R)) = QuotientGroup.mk ⟨O.φ s, hφs⟩ := by
    apply QuotientGroup.eq.2
    change (h : G)⁻¹ * O.φ s ∈ secP O R
    rw [hrs]
    refine ⟨r⁻¹, inv_mem hr, ?_⟩
    have hcomm : O.φ r * O.φ s = O.φ s * O.φ r := O.φ_comm_iff.2 (hR.comm_fixSub hr hs)
    rw [map_inv, hcomm]
    group
  rw [hmk]
  rcases hs1 with rfl | rfl
  · have : (⟨O.φ 1, hφs⟩ : ↥(centralizer (secP O R : Set G))) = 1 := Subtype.ext (map_one _)
    rw [this, QuotientGroup.mk_one]
    exact one_mem _
  · have : (⟨O.φ (OverData.tau m), hφs⟩ : ↥(centralizer (secP O R : Set G))) =
        ⟨z, z_mem_secY O hR⟩ := Subtype.ext O.φ_tau
    rw [this]
    exact mem_zpowers _

end ShapeHyp

section ExactShape

variable {G : Type} [Group G] [Finite G] {z : G} {m : ℕ} (O : OverData G z m)
  {R : Subgroup (Perm (Fin (m + 3)))} (hR : SecR m R)

theorem exactShape_secQ (hm : 10 ≤ m) :
    ExactShape (QuotientGroup.mk (secT O hR) : secQ (secP O R) ⧸ CFSG.oddCore (secQ (secP O R)))
      ((secB O hR).map (QuotientGroup.mk' (CFSG.oddCore (secQ (secP O R))))) (m - 3) :=
  exactShape_quotient_oddCore (orderOf_secT O hR) (by omega) (secBEquiv O hR)
    (secB_le_cent O hR) (cent_secT_le_normalizer O hR hm)
    ((cent_secB_inf_le O hR hm).trans le_sup_left)

end ExactShape

end CFSG.OddStandard.AltStdSec
