module

public import Mathlib.GroupTheory.Nilpotent
import CFSG.LocalAnalysis.SectionRank.CentralLift
import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.FourSixteen

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

private theorem exists_iterate_eq_one {S : Subgroup G} (hS : IsPGroup p S) {x : G} (hx : x ∈ S)
    {y : G} (hy : y ∈ S) : ∃ n : ℕ, (fun z => z⁻¹ * x * z * x⁻¹)^[n] y = 1 := by
  obtain ⟨c, hc⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries S).1 hS.isNilpotent
  refine ⟨c, ?_⟩
  have hmem : ∀ n, (fun z => z⁻¹ * x * z * x⁻¹)^[n] y ∈ S.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      rw [Function.iterate_succ_apply', Subgroup.lowerCentralSeries_succ]
      have := Subgroup.commutator_mem_commutator (inv_mem ih) hx
      simpa [commutatorElement_def] using this
  have := hmem c
  rwa [hc, Subgroup.mem_bot] at this

theorem isMulCommutative_of_card_lt {H : Subgroup G} (hH : IsPGroup p H)
    (h : Nat.card H < p ^ 3) : IsMulCommutative H := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hH
  have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 (hk ▸ h)
  interval_cases k
  · haveI : Subsingleton H := (Nat.card_eq_one_iff_unique.1 (by simpa using hk)).1
    exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
  · haveI := isCyclic_of_prime_card (α := H) (by simpa using hk)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hk

private theorem exists_normal_le_card_lt {R : Subgroup G} (hR : IsPGroup p R)
    (hnc : ¬ IsMulCommutative R) {x : G} (hx : x ∈ R) (hxp : x ^ p = 1) :
    ∃ K : Subgroup G, K ≤ R ∧ x ∈ K ∧ Nat.card K < Nat.card R ∧
      ∀ g ∈ R, ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hR
  have hk3 : 3 ≤ k := by
    by_contra h
    exact hnc (isMulCommutative_of_card_lt hR (by
      rw [hk]; exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)))
  set H : Subgroup R := zpowers ⟨x, hx⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (hR.to_subgroup H)
  have hn1 : n ≤ 1 := by
    have h1 : Nat.card H ∣ p := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxp))
    rw [hn] at h1
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 (by simpa using h1)
  obtain ⟨K', hK'c, hHK'⟩ := Sylow.exists_subgroup_card_pow_prime_le p (m := k - 1)
    (by rw [hk]; exact Nat.pow_dvd_pow p (Nat.sub_le k 1)) H hn (by omega)
  have hidx : K'.index = p := by
    have h1 := Subgroup.card_mul_index K'
    rw [hK'c, hk] at h1
    have h2 : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h1
  have hN : K'.Normal := by
    refine Subgroup.normal_of_index_eq_minFac_card ?_
    rw [hidx, hk, Nat.pow_minFac (by omega), hp.out.minFac_eq]
  refine ⟨K'.map R.subtype, map_subtype_le K', ⟨⟨x, hx⟩, hHK' (mem_zpowers _), rfl⟩, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective R.subtype_injective, hK'c, hk]
    exact Nat.pow_lt_pow_right hp.out.one_lt (by omega)
  · rintro g hg _ ⟨k', hk', rfl⟩
    exact ⟨⟨g, hg⟩ * k' * ⟨g, hg⟩⁻¹, hN.conj_mem k' hk' _, rfl⟩

theorem pow_eq_one_of_mem_closure {s : Set G} (hcomm : s.Pairwise Commute)
    (hs : ∀ a ∈ s, a ^ p = 1) {g : G} (hg : g ∈ closure s) : g ^ p = 1 := by
  have hab := isMulCommutative_closure hcomm
  induction hg using Subgroup.closure_induction with
  | mem a ha => exact hs a ha
  | one => exact one_pow p
  | mul a b ha hb iha ihb =>
    have hc : a * b = b * a := by
      simpa using congrArg Subtype.val (hab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [(Commute.mul_pow hc p), iha, ihb, one_mul]
  | inv a _ iha => rw [inv_pow, iha, inv_one]

private theorem pow_eq_pow_mod {g : G} (hg : g ^ p = 1) (a : ℕ) : g ^ a = g ^ (a % p) := by
  conv_lhs => rw [← Nat.mod_add_div a p, pow_add, pow_mul, hg, one_pow, mul_one]

private theorem heis_of_rel (hp2 : p ≠ 2) {Q : Subgroup G} (hQ : IsPGroup p Q) {w y c : G}
    (hwQ : w ∈ Q) (hyQ : y ∈ Q) (hwp : w ^ p = 1) (hyp : y ^ p = 1) (hcp : c ^ p = 1)
    (hrel : y * w * y⁻¹ = w * c) (hc1 : c ≠ 1) (hwc : w * c = c * w) (hyc : y * c = c * y) :
    ∃ E : Subgroup G, E ≤ Q ∧ Nat.card E = p ^ 3 ∧ (∀ e ∈ E, e ^ p = 1) ∧
      ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
  set E := closure ({w, y} : Set G) with hEdef
  have hwE : w ∈ E := subset_closure (Set.mem_insert _ _)
  have hyE : y ∈ E := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hcw : c = w⁻¹ * (y * w * y⁻¹) := by rw [hrel]; group
  have hcE : c ∈ E := by
    rw [hcw]
    exact mul_mem (inv_mem hwE) (mul_mem (mul_mem hyE hwE) (inv_mem hyE))
  have hEQ : E ≤ Q := closure_le _ |>.2 (Set.insert_subset_iff.2 ⟨hwQ, by simpa using hyQ⟩)
  have hnc : w * y ≠ y * w := by
    intro h
    apply hc1
    rw [hcw, ← h]
    group
  let S : Set G := {g | ∃ a b k : ℕ, g = w ^ a * c ^ b * y ^ k}
  have hSw : ∀ g ∈ S, w * g ∈ S := by
    rintro _ ⟨a, b, k, rfl⟩
    exact ⟨a + 1, b, k, by rw [pow_succ']; group⟩
  have hSy : ∀ g ∈ S, y * g ∈ S := by
    rintro _ ⟨a, b, k, rfl⟩
    refine ⟨a, a + b, k + 1, ?_⟩
    have h1 : y * w ^ a * y⁻¹ = w ^ a * c ^ a := by
      rw [← conj_pow, hrel, (Commute.mul_pow hwc a)]
    have h2 : y * c ^ b = c ^ b * y := ((show Commute y c from hyc).pow_right b).eq
    calc y * (w ^ a * c ^ b * y ^ k) = (y * w ^ a * y⁻¹) * (y * c ^ b) * y ^ k := by group
      _ = w ^ a * c ^ a * (c ^ b * y) * y ^ k := by rw [h1, h2]
      _ = w ^ a * c ^ (a + b) * y ^ (k + 1) := by rw [pow_add, pow_succ']; group
  have hSw' : ∀ j, ∀ g ∈ S, w ^ j * g ∈ S := by
    intro j
    induction j with
    | zero => intro g hg; simpa using hg
    | succ j ih => intro g hg; rw [pow_succ', mul_assoc]; exact hSw _ (ih g hg)
  have hSy' : ∀ j, ∀ g ∈ S, y ^ j * g ∈ S := by
    intro j
    induction j with
    | zero => intro g hg; simpa using hg
    | succ j ih => intro g hg; rw [pow_succ', mul_assoc]; exact hSy _ (ih g hg)
  have hinv : ∀ {g : G}, g ^ p = 1 → g⁻¹ = g ^ (p - 1) := fun {g} hg => by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le, hg]
  have hES : ∀ g ∈ E, g ∈ S := by
    intro g hg
    induction hg using Subgroup.closure_induction_left with
    | one => exact ⟨0, 0, 0, by simp⟩
    | mul_left x hx g _ ih =>
      rcases hx with rfl | rfl
      · exact hSw _ ih
      · exact hSy _ ih
    | inv_mul_cancel x hx g _ ih =>
      rcases hx with rfl | rfl
      · rw [hinv hwp]; exact hSw' _ _ ih
      · rw [hinv hyp]; exact hSy' _ _ ih
  have hle : Nat.card E ≤ p ^ 3 := by
    let f : Fin p × Fin p × Fin p → E := fun t =>
      ⟨w ^ (t.1 : ℕ) * c ^ (t.2.1 : ℕ) * y ^ (t.2.2 : ℕ),
        mul_mem (mul_mem (pow_mem hwE _) (pow_mem hcE _)) (pow_mem hyE _)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨a, b, k, rfl⟩ := hES g hg
      haveI : NeZero p := ⟨hp.out.ne_zero⟩
      refine ⟨(⟨a % p, Nat.mod_lt _ hp.out.pos⟩, ⟨b % p, Nat.mod_lt _ hp.out.pos⟩,
        ⟨k % p, Nat.mod_lt _ hp.out.pos⟩), Subtype.ext ?_⟩
      change w ^ (a % p) * c ^ (b % p) * y ^ (k % p) = _
      rw [← pow_eq_pow_mod hwp, ← pow_eq_pow_mod hcp, ← pow_eq_pow_mod hyp]
    have := Nat.card_le_card_of_surjective f hf
    simpa [Nat.card_prod, pow_succ, mul_assoc] using this
  have hEp : IsPGroup p E := hQ.to_le hEQ
  have hncE : ¬ IsMulCommutative E := fun h =>
    hnc (by simpa using congrArg Subtype.val (h.is_comm.comm ⟨w, hwE⟩ ⟨y, hyE⟩))
  have hcard : Nat.card E = p ^ 3 := by
    refine le_antisymm hle ?_
    by_contra h
    exact hncE (isMulCommutative_of_card_lt hEp (by omega))
  have hnc' : ∃ a b : E, a * b ≠ b * a :=
    ⟨⟨w, hwE⟩, ⟨y, hyE⟩, fun h => hnc (by simpa using congrArg Subtype.val h)⟩
  obtain ⟨hZ, hZc, -⟩ := CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hcard hnc'
  have hcen : ∀ a b : E, ⁅a, b⁆ ∈ center E := fun a b => by
    rw [← hZ, commutator_def]
    exact commutator_mem_commutator (mem_top a) (mem_top b)
  have hcc : ∀ a b z : E, Commute ⁅a, b⁆ z := fun a b z =>
    ((Subgroup.mem_center_iff.1 (hcen a b)) z).symm
  have hcpE : ∀ a b : E, ⁅a, b⁆ ^ p = 1 := fun a b => by
    have h := pow_card_eq_one' (G := center E) (x := ⟨_, hcen a b⟩)
    rw [hZc] at h
    simpa using congrArg Subtype.val h
  let φ := CFSG.SectionRank.powHom hcc hp.out hp2 hcpE
  have hker : (⊤ : Subgroup E) ≤ φ.ker := by
    rw [← closure_closure_coe_preimage (k := ({w, y} : Set G)), closure_le]
    rintro ⟨g, hg⟩ hgs
    rcases hgs with h | h
    · exact Subtype.ext (by simp [φ, CFSG.SectionRank.powHom, show g = w from h, hwp])
    · exact Subtype.ext (by simp [φ, CFSG.SectionRank.powHom, show g = y from h, hyp])
  refine ⟨E, hEQ, hcard, fun e he => ?_, w, hwE, y, hyE, hnc⟩
  have := hker (mem_top ⟨e, he⟩)
  simpa [φ, CFSG.SectionRank.powHom] using congrArg Subtype.val (MonoidHom.mem_ker.1 this)

theorem exists_heis_of_not_commute (hp2 : p ≠ 2) {Q : Subgroup G} (hQ : IsPGroup p Q) {x y : G}
    (hxQ : x ∈ Q) (hyQ : y ∈ Q) (hxp : x ^ p = 1) (hyp : y ^ p = 1) (hxy : x * y ≠ y * x) :
    ∃ E : Subgroup G, E ≤ Q ∧ Nat.card E = p ^ 3 ∧ (∀ e ∈ E, e ^ p = 1) ∧
      ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a := by
  suffices h : ∀ n, ∀ x y : G, Nat.card (closure ({x, y} : Set G)) = n → x ∈ Q → y ∈ Q →
      x ^ p = 1 → y ^ p = 1 → x * y ≠ y * x → ∃ E : Subgroup G, E ≤ Q ∧ Nat.card E = p ^ 3 ∧
        (∀ e ∈ E, e ^ p = 1) ∧ ∃ a ∈ E, ∃ b ∈ E, a * b ≠ b * a from
    h _ x y rfl hxQ hyQ hxp hyp hxy
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro x y hn hxQ hyQ hxp hyp hxy
  set R := closure ({x, y} : Set G) with hRdef
  have hxR : x ∈ R := subset_closure (Set.mem_insert _ _)
  have hyR : y ∈ R := subset_closure (Set.mem_insert_of_mem _ rfl)
  have hRQ : R ≤ Q := closure_le _ |>.2 (Set.insert_subset_iff.2 ⟨hxQ, by simpa using hyQ⟩)
  have hR : IsPGroup p R := hQ.to_le hRQ
  have hnc : ¬ IsMulCommutative R := fun h =>
    hxy (by simpa using congrArg Subtype.val (h.is_comm.comm ⟨x, hxR⟩ ⟨y, hyR⟩))
  obtain ⟨K, hKR, hxK, hKc, hKn⟩ := exists_normal_le_card_lt hR hnc hxR hxp
  set u : ℕ → G := fun i => y ^ i * x * (y ^ i)⁻¹ with hu
  have huK : ∀ i, u i ∈ K := fun i => hKn _ (pow_mem hyR i) _ hxK
  have hup : ∀ i, u i ^ p = 1 := fun i => by simp [u, conj_pow, hxp]
  by_cases hcase : ∃ i, x * u i ≠ u i * x
  · obtain ⟨i, hi⟩ := hcase
    have hle : closure ({x, u i} : Set G) ≤ K :=
      (closure_le _).2 (Set.insert_subset_iff.2 ⟨hxK, Set.singleton_subset_iff.2 (huK i)⟩)
    have hlt : Nat.card (closure ({x, u i} : Set G)) < n :=
      hn ▸ (Subgroup.card_le_of_le hle).trans_lt hKc
    exact ih _ hlt x (u i) rfl hxQ (hRQ (hKR (huK i))) hxp (hup i) hi
  push Not at hcase
  have hshift : ∀ i d, u (i + d) = y ^ i * u d * (y ^ i)⁻¹ := fun i d => by
    simp only [u, pow_add]; group
  have hcomm2 : ∀ i d, u i * u (i + d) = u (i + d) * u i := by
    intro i d
    have h := (show Commute x (u d) from hcase d).map (MulAut.conj (y ^ i)).toMonoidHom
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [hshift]
    have e : u i = y ^ i * x * (y ^ i)⁻¹ := rfl
    rw [e]
    exact h.eq
  have hcomm : (Set.range u).Pairwise Commute := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ -
    rcases le_total i j with h | h
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      exact hcomm2 i d
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
      exact (hcomm2 j d).symm
  set N₀ := closure (Set.range u) with hN₀
  have hNab := isMulCommutative_closure hcomm
  have hNcomm : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := fun a ha b hb => by
    simpa using congrArg Subtype.val (hNab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hNexp : ∀ a ∈ N₀, a ^ p = 1 := fun a ha =>
    pow_eq_one_of_mem_closure hcomm (by rintro _ ⟨i, rfl⟩; exact hup i) ha
  have hNy : ∀ a ∈ N₀, y * a * y⁻¹ ∈ N₀ := by
    have hle : N₀ ≤ N₀.comap (MulAut.conj y).toMonoidHom := by
      rw [hN₀, closure_le]
      rintro _ ⟨i, rfl⟩
      show y * u i * y⁻¹ ∈ N₀
      have : y * u i * y⁻¹ = u (1 + i) := by rw [hshift]; simp
      rw [this]
      exact subset_closure ⟨_, rfl⟩
    exact fun a ha => hle ha
  have hNR : N₀ ≤ R := (closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hKR (huK i))
  set F : G → G := fun z => z⁻¹ * y * z * y⁻¹ with hF
  have hFN : ∀ z ∈ N₀, F z ∈ N₀ := fun z hz => by
    have e : F z = z⁻¹ * (y * z * y⁻¹) := by simp only [F]; group
    rw [e]
    exact mul_mem (inv_mem hz) (hNy z hz)
  have hxN : x ∈ N₀ := subset_closure ⟨0, by simp [u]⟩
  have hit : ∀ k, F^[k] x ∈ N₀ := fun k => by
    induction k with
    | zero => exact hxN
    | succ k ih => rw [Function.iterate_succ_apply']; exact hFN _ ih
  have hex : ∃ n, F^[n] x = 1 := exists_iterate_eq_one hQ hyQ hxQ
  classical
  set m₀ := Nat.find hex with hm₀
  have hm₀1 : F^[m₀] x = 1 := Nat.find_spec hex
  have hx1 : x ≠ 1 := by rintro rfl; simp at hxy
  have hFx : F x ≠ 1 := fun h => hxy (by
    have h' : x⁻¹ * y * x * y⁻¹ = 1 := h
    have : y * x = x * y := by
      calc y * x = x * (x⁻¹ * y * x * y⁻¹) * y := by group
        _ = x * y := by rw [h', mul_one]
    exact this.symm)
  have h2 : 2 ≤ m₀ := by
    by_contra h
    interval_cases hm : m₀
    · exact hx1 (by simpa using hm₀1)
    · exact hFx (by simpa using hm₀1)
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h2
  set w := F^[m] x with hw
  set c := F w with hc
  have hc1 : c ≠ 1 := by
    have := Nat.find_min hex (show m + 1 < Nat.find hex by omega)
    rwa [Function.iterate_succ_apply'] at this
  have hFc : F c = 1 := by
    rw [hm, show 2 + m = m + 1 + 1 by omega, Function.iterate_succ_apply',
      Function.iterate_succ_apply'] at hm₀1
    exact hm₀1
  have hwN : w ∈ N₀ := hit m
  have hcN : c ∈ N₀ := hFN w hwN
  have hyc : y * c = c * y := by
    have h' : c⁻¹ * y * c * y⁻¹ = 1 := hFc
    calc y * c = c * (c⁻¹ * y * c * y⁻¹) * y := by group
      _ = c * y := by rw [h', mul_one]
  have hrel : y * w * y⁻¹ = w * c := by
    have e : c = w⁻¹ * y * w * y⁻¹ := rfl
    rw [e]; group
  exact heis_of_rel hp2 hQ (hRQ (hNR hwN)) hyQ (hNexp w hwN) hyp (hNexp c hcN) hrel hc1
    (hNcomm w hwN c hcN) hyc

end CFSG.LocalAnalysis.RankThreeTheoremC.FourSixteen
