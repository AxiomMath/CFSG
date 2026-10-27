module

public import CFSG.GH74.QTGen4.DSGen4.LeafWrappersAmal

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

private def dslgRestrict {G H : Type} [Group G] [Group H] {P : Subgroup G} {M : Subgroup H}
    (e : ↥P ≃* ↥M) {K : Subgroup G} (hK : K ≤ P) {K' : Subgroup H} (hK' : K' ≤ M)
    (h : ∀ x : ↥P, (x : G) ∈ K ↔ ((e x : ↥M) : H) ∈ K') : ↥K ≃* ↥K' where
  toFun x := ⟨((e ⟨x.1, hK x.2⟩ : ↥M) : H), (h ⟨x.1, hK x.2⟩).1 x.2⟩
  invFun y := ⟨(e.symm ⟨y.1, hK' y.2⟩ : G), (h (e.symm ⟨y.1, hK' y.2⟩)).2 (by simpa using y.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    have h := congrArg Subtype.val (map_mul e ⟨x.1, hK x.2⟩ ⟨y.1, hK y.2⟩)
    exact h

theorem leafL34Glue [DSLeaf LeafL34DC] : LeafL34Glue := by
  intro Mdl hMdl G _ _ P1 P2 S Q1 Q2 ψ₁ ψ₂ hSP1 hSP2 hQ1S hQ2P hQ1e hQ1c hne hS1 hS2 hB1 hB2 hQ1 hQ2
  have hQ1P2 : Q1 ≤ P2 := hQ1S.trans hSP2
  let ι₂ : ↥P2 →* Mdl.Y := Mdl.M2.subtype.comp (ψ₂ : ↥P2 ≃* ↥Mdl.M2).toMonoidHom
  have hι₂ : Function.Injective ι₂ := by
    intro x y h
    apply ψ₂.injective
    apply Subtype.ext
    exact h
  set E : Subgroup Mdl.Y := (Q1.subgroupOf P2).map ι₂ with hE_def
  have hEmem : ∀ y : ↥P2, (y : G) ∈ Q1 ↔ ι₂ y ∈ E := by
    intro y
    rw [hE_def, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      rw [hι₂ hzy] at hz
      exact Subgroup.mem_subgroupOf.mp hz
  have hET0 : E ≤ Mdl.T0 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
    exact (hS2 y).1 (hQ1S (Subgroup.mem_subgroupOf.mp hy))
  have hEab : IsElemAbelian 2 E := by
    obtain ⟨hcomm, hexp⟩ := hQ1e
    unfold IsElemAbelian
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hb
      apply Subtype.ext
      show ι₂ y * ι₂ y' = ι₂ y' * ι₂ y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      have h := congrArg Subtype.val (isMulCommutative_iff.mp hcomm
        ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩ ⟨(y' : G), Subgroup.mem_subgroupOf.mp hy'⟩)
      exact h
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      have hy2 : y ^ 2 = 1 := Subtype.ext (by simpa using hexp _ (Subgroup.mem_subgroupOf.mp hy))
      rw [← map_pow, hy2, map_one]
  have hEcard : Nat.card E = 16 := by
    rw [hE_def, Subgroup.card_map_of_injective hι₂,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ1P2).toEquiv]
    exact hQ1c
  have hcase := hMdl.only E hET0 hEab hEcard
  have hKEY : ∀ y : ↥P2, (y : G) ∈ Q1 ↔ ((ψ₂ y : ↥Mdl.M2) : Mdl.Y) ∈ pCoreOf 2 Mdl.M1 := by
    rcases hcase with h1 | h2
    · intro y
      have h := hEmem y
      rw [h1] at h
      exact h
    · exfalso
      apply hne
      ext g
      constructor
      · intro hg
        have hgP2 : g ∈ P2 := hQ1P2 hg
        have hm : ι₂ ⟨g, hgP2⟩ ∈ E := (hEmem ⟨g, hgP2⟩).1 hg
        rw [h2] at hm
        exact (hQ2 ⟨g, hgP2⟩).2 hm
      · intro hg
        have hgP2 : g ∈ P2 := hQ2P hg
        have hm : ι₂ ⟨g, hgP2⟩ ∈ E := by
          rw [h2]
          exact (hQ2 ⟨g, hgP2⟩).1 hg
        exact (hEmem ⟨g, hgP2⟩).2 hm
  have hψ₁B : ∀ x : ↥P1, (x : G) ∈ P1 ⊓ P2 ↔ ((ψ₁ x : ↥Mdl.M1) : Mdl.Y) ∈ Mdl.M1 ⊓ Mdl.M2 := by
    intro x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨(ψ₁ x).2, (hB1 x).1 h.2⟩, fun h => ⟨x.2, (hB1 x).2 h.2⟩⟩
  have hψ₂B : ∀ x : ↥P2, (x : G) ∈ P1 ⊓ P2 ↔ ((ψ₂ x : ↥Mdl.M2) : Mdl.Y) ∈ Mdl.M1 ⊓ Mdl.M2 := by
    intro x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨(hB2 x).1 h.1, (ψ₂ x).2⟩, fun h => ⟨(hB2 x).2 h.1, x.2⟩⟩
  let βψ₁ : ↥(P1 ⊓ P2) ≃* ↥(Mdl.M1 ⊓ Mdl.M2) :=
    dslgRestrict ψ₁ (inf_le_left : P1 ⊓ P2 ≤ P1) (inf_le_left : Mdl.M1 ⊓ Mdl.M2 ≤ Mdl.M1) hψ₁B
  let βψ₂ : ↥(P1 ⊓ P2) ≃* ↥(Mdl.M1 ⊓ Mdl.M2) :=
    dslgRestrict ψ₂ (inf_le_right : P1 ⊓ P2 ≤ P2) (inf_le_right : Mdl.M1 ⊓ Mdl.M2 ≤ Mdl.M2) hψ₂B
  let γ : ↥(Mdl.M1 ⊓ Mdl.M2) ≃* ↥(Mdl.M1 ⊓ Mdl.M2) := βψ₁.symm.trans βψ₂
  have hγz : ∀ z : ↥(P1 ⊓ P2), γ (βψ₁ z) = βψ₂ z := by
    intro z
    show βψ₂ (βψ₁.symm (βψ₁ z)) = βψ₂ z
    rw [MulEquiv.symm_apply_apply]
  have hσ : ∀ b : ↥(Mdl.M1 ⊓ Mdl.M2), (b : Mdl.Y) ∈ pCoreOf 2 Mdl.M1 ↔
      ((γ b : ↥(Mdl.M1 ⊓ Mdl.M2)) : Mdl.Y) ∈ pCoreOf 2 Mdl.M1 := by
    intro b
    obtain ⟨z, rfl⟩ := βψ₁.surjective b
    rw [hγz z]
    exact (hQ1 ⟨(z : G), z.2.1⟩).symm.trans (hKEY ⟨(z : G), z.2.2⟩)
  obtain ⟨a₁, a₂, hA1, hA2, hA3⟩ := l34_dc Mdl hMdl γ hσ
  let A₁ : ↥(Mdl.M1 ⊓ Mdl.M2) ≃* ↥(Mdl.M1 ⊓ Mdl.M2) :=
    dslgRestrict a₁ (inf_le_left : Mdl.M1 ⊓ Mdl.M2 ≤ Mdl.M1) (inf_le_left : Mdl.M1 ⊓ Mdl.M2 ≤ Mdl.M1)
      (by
        intro m
        simp only [Subgroup.mem_inf]
        exact ⟨fun h => ⟨(a₁ m).2, (hA1 m).1 h.2⟩, fun h => ⟨m.2, (hA1 m).2 h.2⟩⟩)
  let A₂ : ↥(Mdl.M1 ⊓ Mdl.M2) ≃* ↥(Mdl.M1 ⊓ Mdl.M2) :=
    dslgRestrict a₂ (inf_le_right : Mdl.M1 ⊓ Mdl.M2 ≤ Mdl.M2) (inf_le_right : Mdl.M1 ⊓ Mdl.M2 ≤ Mdl.M2)
      (by
        intro m
        simp only [Subgroup.mem_inf]
        exact ⟨fun h => ⟨(hA2 m).1 h.1, (a₂ m).2⟩, fun h => ⟨(hA2 m).2 h.1, m.2⟩⟩)
  have hγ2 : ∀ c : ↥(Mdl.M1 ⊓ Mdl.M2), A₂ (A₁ c) = γ c := by
    intro c
    apply Subtype.ext
    exact hA3 c ⟨(c : Mdl.Y), c.2.1⟩ ⟨((A₁ c : ↥(Mdl.M1 ⊓ Mdl.M2)) : Mdl.Y), (A₁ c).2.2⟩ rfl rfl
  let φ1 : ↥P1 ≃* ↥Mdl.M1 := ψ₁.trans a₁
  let φ2 : ↥P2 ≃* ↥Mdl.M2 := ψ₂.trans (MulEquiv.symm a₂)
  let φ12 : ↥(P1 ⊓ P2) ≃* ↥(Mdl.M1 ⊓ Mdl.M2) := βψ₁.trans A₁
  refine ⟨⟨φ1, φ12, φ2, ?_, ?_⟩⟩
  · intro g
    apply Subtype.ext
    rfl
  · intro g
    have hm : a₂ ⟨(A₁ (βψ₁ g)).1, (A₁ (βψ₁ g)).2.2⟩ = ψ₂ ⟨g.1, g.2.2⟩ := by
      apply Subtype.ext
      have h := congrArg Subtype.val ((hγ2 (βψ₁ g)).trans (hγz g))
      exact h
    have hm' : (⟨(A₁ (βψ₁ g)).1, (A₁ (βψ₁ g)).2.2⟩ : ↥Mdl.M2) =
        MulEquiv.symm a₂ (ψ₂ ⟨g.1, g.2.2⟩) :=
      (MulEquiv.eq_symm_apply a₂).mpr hm
    apply Subtype.ext
    exact congrArg Subtype.val hm'

end CFSG.GH74.QTGen4.DSGen4
