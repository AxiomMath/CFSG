module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModule.TwoThreeCore

public section

namespace CFSG.CGT.PushingUpLit.CGT6.TwoThree

open CFSG.Quasithin CFSG.SL2MinimalFaithful Matrix

namespace NatData

variable {K : Type*} [Field K] {V : Type} [CommGroup V] {G : Subgroup (MulAut V)}
  (D : NatData K G)

@[expose] def conj (g : SpecialLinearGroup (Fin 2) K) : NatData K G where
  ρ := D.ρ.comp (MulAut.conj g).toMonoidHom
  range_eq := by
    have : (D.ρ.comp (MulAut.conj g).toMonoidHom).range = D.ρ.range := by
      ext x
      constructor
      · rintro ⟨m, rfl⟩
        exact ⟨_, rfl⟩
      · rintro ⟨m, rfl⟩
        refine ⟨g⁻¹ * m * g, ?_⟩
        simp [MulAut.conj_apply, mul_assoc]
    rw [this, D.range_eq]
  inj := D.inj.comp (MulAut.conj g).injective
  β := (matHom g⁻¹).comp D.β
  surj := by
    intro w
    obtain ⟨u, hu⟩ := D.surj (matHom g w)
    refine ⟨u, ?_⟩
    rw [MonoidHom.comp_apply, hu, ← matHom_mul, inv_mul_cancel, matHom_one]
  ker := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, matHom_eq_one_iff, ← MonoidHom.mem_ker, D.ker]
  equiv := by
    intro m u hu
    have h : D.β ⟨D.ρ (g * m * g⁻¹) u, hu⟩ = matHom (g * m * g⁻¹) (D.β u) :=
      D.equiv (g * m * g⁻¹) u hu
    show matHom g⁻¹ (D.β ⟨D.ρ (g * m * g⁻¹) u, hu⟩) = matHom m (matHom g⁻¹ (D.β u))
    rw [h, ← matHom_mul, ← matHom_mul]
    congr 1
    group

section ConjT

variable [CharP K 2] [Finite K] [Finite V]

theorem exists_conj_T_eq {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT : Nat.card T = Nat.card K) :
    ∃ g : SpecialLinearGroup (Fin 2) K, (D.conj g).T = T := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  have hU : Nat.card (T.comap D.ρ) = Nat.card K := by
    rw [← hT]
    refine Nat.card_congr (Equiv.ofBijective
      (fun x : T.comap D.ρ => (⟨D.ρ x, x.2⟩ : T)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext (D.inj (congrArg Subtype.val hxy))
    · rintro ⟨t, ht⟩
      have : t ∈ D.ρ.range := by rw [D.range_eq]; exact hTG ht
      obtain ⟨m, rfl⟩ := this
      exact ⟨⟨m, ht⟩, rfl⟩
  obtain ⟨g, hg⟩ := exists_conj_unipotent_mem hp hcard hU
  have hle : (D.conj g).T ≤ T := by
    intro x hx
    obtain ⟨s, rfl⟩ := (D.conj g).mem_T.mp hx
    exact hg s
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [(D.conj g).card_T, hT]

include D in
theorem sylow_facts_of_card (hV : ∀ v : V, v ^ 2 = 1) (h4 : 4 ≤ Nat.card K)
    {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT : Nat.card T = Nat.card K) :
    IsElemAbelian2 T ∧ commV T ≤ fixV T ∧ commV T = commV G ⊓ fixV T ∧
      ∀ B : Subgroup (MulAut V), B ≤ T → 4 ≤ Nat.card B → commV B = commV T := by
  obtain ⟨g, hg⟩ := D.exists_conj_T_eq hTG hT
  have := (D.conj g).sylow_facts hV h4
  rwa [hg] at this

end ConjT

end NatData

end CFSG.CGT.PushingUpLit.CGT6.TwoThree

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG.Quasithin

open CFSG.CGT.PushingUpLit.BHS6 in
theorem exists_natData {V : Type} [CommGroup V] {G : Subgroup (MulAut V)} {n : ℕ}
    (hnat : IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (x : Multiplicative (Fin 2 → GaloisField 2 n)) => Multiplicative.ofAdd
        ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd x))) G
      (commV G) (commV G ⊓ fixV G)) :
    Nonempty (TwoThree.NatData (GaloisField 2 n) G) := by
  obtain ⟨-, θ, β, hβs, hβk, hβe⟩ := hnat
  exact ⟨{ ρ := G.subtype.comp θ.symm.toMonoidHom
           range_eq := by
             ext g
             constructor
             · rintro ⟨m, rfl⟩
               exact (θ.symm m).2
             · intro hg
               exact ⟨θ ⟨g, hg⟩, by simp⟩
           inj := fun a b h => θ.symm.injective (Subtype.ext h)
           β := β
           surj := hβs
           ker := hβk
           equiv := by
             intro m u hu
             have := hβe (θ.symm m) u hu
             simpa using this }⟩

open CFSG.CGT.PushingUpLit.BHS6 in
theorem emb_two_three_sylow {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G : Subgroup (MulAut V)) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (x : Multiplicative (Fin 2 → GaloisField 2 n)) => Multiplicative.ofAdd
        ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd x))) G
      (commV G) (commV G ⊓ fixV G))
    {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT : Nat.card T = 2 ^ n) :
    IsElemAbelian2 T ∧ commV T ≤ fixV T ∧ commV T = commV G ⊓ fixV T ∧
      ∀ B : Subgroup (MulAut V), B ≤ T → 4 ≤ Nat.card B → commV B = commV T := by
  obtain ⟨D⟩ := exists_natData hnat
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h4 : 4 ≤ Nat.card (GaloisField 2 n) := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  exact D.sylow_facts_of_card hV h4 hTG (by rw [hT, hK])

open CFSG.CGT.PushingUpLit.BHS6 in
theorem emb_two_three_hyperplane {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    (G : Subgroup (MulAut V)) {n : ℕ} (hn : 3 ≤ n)
    (hnat : IsNatSectionBy (fun (s : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (x : Multiplicative (Fin 2 → GaloisField 2 n)) => Multiplicative.ofAdd
        ((s : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec (Multiplicative.toAdd x))) G
      (commV G) (commV G ⊓ fixV G))
    {T : Subgroup (MulAut V)} (hTG : T ≤ G) (hT : Nat.card T = 2 ^ n) (B : Subgroup T)
    (hB : B.index = 2) : commV T ≤ commV (B.map T.subtype) := by
  have h1 : Nat.card B * 2 = 2 ^ n := by
    have := B.card_mul_index
    rwa [hB, hT] at this
  have h2 : 4 ≤ Nat.card (B.map T.subtype) := by
    rw [Subgroup.card_map_of_injective T.subtype_injective]
    have h3 : 2 ^ n = 2 ^ (n - 3) * 8 := by
      rw [← pow_sub_mul_pow 2 hn]
      norm_num
    have h4 : 1 ≤ 2 ^ (n - 3) := Nat.one_le_two_pow
    omega
  exact ((emb_two_three_sylow hV G (by omega) hnat hTG hT).2.2.2 _ (Subgroup.map_subtype_le B)
    h2).ge

end CFSG.CGT.PushingUpLit.CGT6
