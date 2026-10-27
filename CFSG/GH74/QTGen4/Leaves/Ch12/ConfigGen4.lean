module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.Vol2.Ch12Sec2ChainStmts

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.Open CFSG.Quasithin.H13

theorem card_le_sixteen_of_isElemAbelian {G : Type} [Group G] [Finite4 G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : Nat.card E ≤ 16 :=
  (Finite4.gen4 (G := G) : SectionalTwoRankLE G 4).card_le_of_elementary E hE

theorem card_inf_mul_card_inf_le_card {G : Type} [Group G] [Finite G] {U V W : Subgroup G}
    (hUi : (U ⊓ V) ⊓ (U ⊓ W) = ⊥) :
    Nat.card ↥(U ⊓ V) * Nat.card ↥(U ⊓ W) ≤ Nat.card U := by
  let f : ↥(U ⊓ V) × ↥(U ⊓ W) → ↥U := fun q =>
    ⟨(q.1 : G) * q.2, U.mul_mem q.1.2.1 q.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    have h' : (a : G) * b = a' * b' := congrArg (fun z : ↥U => (z : G)) hab
    have hrel : ((a' : G)⁻¹ * a : G) = b' * (b : G)⁻¹ := by
      have := congrArg (fun z => (a' : G)⁻¹ * z * (b : G)⁻¹) h'
      simpa [mul_assoc] using this
    have hmem : ((a' : G)⁻¹ * a : G) ∈ (U ⊓ V) ⊓ (U ⊓ W) := by
      refine ⟨(U ⊓ V).mul_mem ((U ⊓ V).inv_mem a'.2) a.2, ?_⟩
      rw [hrel]
      exact (U ⊓ W).mul_mem b'.2 ((U ⊓ W).inv_mem b.2)
    rw [hUi, Subgroup.mem_bot] at hmem
    have haa : (a : G) = a' := (inv_mul_eq_one.mp hmem).symm
    have hbb : (b : G) = b' := by
      have := h'
      rw [haa] at this
      exact mul_left_cancel this
    exact Prod.ext (Subtype.ext haa) (Subtype.ext hbb)
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod] at this

theorem card_inf_conjugate_ge {G : Type} [Group G] [Finite G] {V U I : Subgroup G} {h : G}
    {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hVn : Nat.card V = 2 ^ n)
    (hI : I = V ⊔ CFSG.conjugate V h)
    (hD : ∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p)) :
    2 ^ n ≤ 2 * Nat.card ↥(U ⊓ CFSG.conjugate V h) := by
  obtain ⟨hN, ⟨e⟩⟩ := hD
  set W := CFSG.conjugate V h with hWdef
  have hWn : Nat.card W = 2 ^ n := by
    rw [hWdef]
    unfold CFSG.conjugate
    rw [Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj h⁻¹))]
    exact hVn
  have hW2 : IsPGroup 2 W := IsPGroup.of_card hWn
  have hWI : W ≤ I := hI ▸ le_sup_right
  let φ : ↥W →* ↥I ⧸ U.subgroupOf I :=
    (QuotientGroup.mk' (U.subgroupOf I)).comp (Subgroup.inclusion hWI)
  let ψ : ↥W →* DihedralGroup p := e.toMonoidHom.comp φ
  have hR2 : IsPGroup 2 ↥ψ.range := hW2.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hRd : Nat.card ↥ψ.range ∣ 2 * p := by
    have := Subgroup.card_subgroup_dvd_card ψ.range
    rwa [DihedralGroup.nat_card] at this
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hR1 : Nat.card ↥ψ.range ≤ 2 := by
    rw [hk] at hRd ⊢
    have hcop : Nat.Coprime (2 ^ k) p :=
      Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
    have h2 : 2 ^ k ∣ 2 := hcop.dvd_of_dvd_mul_right hRd
    exact Nat.le_of_dvd (by norm_num) h2
  have hker : Nat.card ↥ψ.ker * Nat.card ↥ψ.range = 2 ^ n := by
    have := Subgroup.card_mul_index ψ.ker
    rwa [Subgroup.index_ker, hWn] at this
  have hkerle : Nat.card ↥ψ.ker ≤ Nat.card ↥(U ⊓ W) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨((x : ↥W) : G), ?_, (x : ↥W).2⟩ : ↥(U ⊓ W))) ?_
    · have h1 : ψ x = 1 := x.2
      have h2 : φ x = 1 :=
        e.injective ((show e (φ x) = 1 from h1).trans (map_one e).symm)
      have h3 : QuotientGroup.mk' (U.subgroupOf I) (Subgroup.inclusion hWI x) = 1 := h2
      have h4 : Subgroup.inclusion hWI x ∈ U.subgroupOf I := (QuotientGroup.eq_one_iff _).mp h3
      exact Subgroup.mem_subgroupOf.mp h4
    · intro x y hxy
      have : ((x : ↥W) : G) = ((y : ↥W) : G) := congrArg (fun z : ↥(U ⊓ W) => (z : G)) hxy
      exact Subtype.ext (Subtype.ext this)
  have hr1 : 1 ≤ Nat.card ↥ψ.range := Nat.card_pos
  calc 2 ^ n = Nat.card ↥ψ.ker * Nat.card ↥ψ.range := hker.symm
    _ ≤ Nat.card ↥ψ.ker * 2 := Nat.mul_le_mul_left _ hR1
    _ ≤ Nat.card ↥(U ⊓ W) * 2 := Nat.mul_le_mul_right _ hkerle
    _ = 2 * Nat.card ↥(U ⊓ W) := by ring

theorem n_eq_three_of_dihedral_gen4 {G : Type} [Group G] [Finite4 G] {V U I : Subgroup G}
    {h : G} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : n = 3 ∨ n = 4 ∨ n = 5)
    (hVn : Nat.card V = 2 ^ n) (hI : I = V ⊔ CFSG.conjugate V h)
    (hUi : (U ⊓ V) ⊓ (U ⊓ CFSG.conjugate V h) = ⊥) (hUe : IsElemAbelian 2 U)
    (hD : ∃ _ : (U.subgroupOf I).Normal, Nonempty (↥I ⧸ U.subgroupOf I ≃* DihedralGroup p))
    (hidx : (U ⊓ V).relIndex V = 2) : n = 3 ∧ 16 ≤ Nat.card U ∧ Nat.card U ≤ 16 := by
  have hU16 := card_le_sixteen_of_isElemAbelian (G := G) hUe
  have hW := card_inf_conjugate_ge hp hp2 hVn hI hD
  have hprod := card_inf_mul_card_inf_le_card hUi
  have hA : Nat.card ↥((U ⊓ V).subgroupOf V) = Nat.card ↥(U ⊓ V) := by
    rw [← Subgroup.card_subtype V ((U ⊓ V).subgroupOf V),
      Subgroup.map_subgroupOf_eq_of_le (inf_le_right : U ⊓ V ≤ V)]
  have h2 : 2 * Nat.card ↥(U ⊓ V) = 2 ^ n := by
    have := Subgroup.card_mul_index ((U ⊓ V).subgroupOf V)
    rw [hA] at this
    have hidx' : ((U ⊓ V).subgroupOf V).index = 2 := hidx
    rw [hidx', hVn] at this
    omega
  generalize Nat.card ↥(U ⊓ V) = a at h2 hprod
  generalize Nat.card ↥(U ⊓ CFSG.conjugate V h) = b at hW hprod
  rcases hn with rfl | rfl | rfl
  · refine ⟨rfl, ?_, hU16⟩
    have ha : a = 4 := by norm_num at h2; omega
    subst ha
    have hb : 4 ≤ b := by norm_num at hW; omega
    nlinarith
  · exfalso
    have ha : a = 8 := by norm_num at h2; omega
    subst ha
    have hb : 8 ≤ b := by norm_num at hW; omega
    nlinarith
  · exfalso
    have ha : a = 16 := by norm_num at h2; omega
    subst ha
    have hb : 16 ≤ b := by norm_num at hW; omega
    nlinarith

theorem n_eq_three_of_config_gen4 {G : Type} [Group G] [Finite4 G]
    {T L V H P U I : Subgroup G} {h : G} {n p : ℕ} (hC : Config12_2_24 T L V H P U I h n p) :
    n = 3 ∧ 16 ≤ Nat.card U ∧ Nat.card U ≤ 16 := by
  obtain ⟨-, -, hn, hVn, -, -, hp, hp2, -, -, -, -, hI, -, -, hUi, hUe, hD, -, hidx, -, -, -, -,
    -, -, -, -, -, -⟩ := hC
  exact n_eq_three_of_dihedral_gen4 hp hp2 hn hVn hI hUi hUe hD hidx

end CFSG.GH74.QTGen4.Leaves
