module

public import CFSG.LargeExtraspecial.AS62C36Am
public import CFSG.LargeExtraspecial.AS62C36Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.U42

namespace AS62

section IndexTwo

variable {A₀ A B₀ B : Type*} [Group A₀] [Group A] [Group B₀] [Group B]

private structure IdxTwo (i : A₀ →* A) (a : A) : Prop where
  inj : Function.Injective i
  sq : a * a = 1
  notMem : a ∉ i.range
  cover : ∀ x : A, x ∈ i.range ∨ x * a ∈ i.range

private theorem IdxTwo.exists_conj {i : A₀ →* A} {a : A} (h : IdxTwo i a) (x : A₀) :
    ∃ x' : A₀, i x' = a * i x * a⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right h.sq]
  rcases h.cover (a * i x * a) with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact ⟨y, hy⟩
  · exfalso
    refine h.notMem ⟨y * x⁻¹, ?_⟩
    rw [map_mul, map_inv, hy]
    calc a * i x * a * a * (i x)⁻¹ = a * i x * (a * a) * (i x)⁻¹ := by group
      _ = a := by rw [h.sq]; group

private theorem IdxTwo.hom_ext {C : Type*} [Group C] {i : A₀ →* A} {a : A} (h : IdxTwo i a)
    {F F' : A →* C} (h0 : ∀ x : A₀, F (i x) = F' (i x)) (h1 : F a = F' a) : F = F' := by
  refine MonoidHom.ext fun x => ?_
  rcases h.cover x with ⟨x₀, hx₀⟩ | ⟨x₀, hx₀⟩
  · rw [← hx₀]
    exact h0 x₀
  · have hx : x = i x₀ * a := by rw [hx₀, mul_assoc, h.sq, mul_one]
    rw [hx, map_mul, map_mul, h0, h1]

open Classical in
private noncomputable def extFun (i : A₀ →* A) (j : B₀ →* B) (ψ : A₀ ≃* B₀) (a : A) (b : B)
    (x : A) : B :=
  if x ∈ i.range then j (ψ (Function.invFun i x)) else j (ψ (Function.invFun i (x * a))) * b

private theorem extFun_i {i : A₀ →* A} {a : A} (hi : Function.Injective i) (j : B₀ →* B)
    (ψ : A₀ ≃* B₀) (b : B) (x : A₀) : extFun i j ψ a b (i x) = j (ψ x) := by
  unfold extFun
  split_ifs with hx
  · rw [Function.leftInverse_invFun hi x]
  · exact absurd ⟨x, rfl⟩ hx

private theorem extFun_i_mul {i : A₀ →* A} {a : A} (h : IdxTwo i a) (j : B₀ →* B)
    (ψ : A₀ ≃* B₀) (b : B) (x : A₀) : extFun i j ψ a b (i x * a) = j (ψ x) * b := by
  have hn : i x * a ∉ i.range := by
    rintro ⟨y, hy⟩
    refine h.notMem ⟨x⁻¹ * y, ?_⟩
    rw [map_mul, map_inv, hy]
    group
  simp only [extFun, hn, ↓reduceIte]
  rw [mul_assoc, h.sq, mul_one, Function.leftInverse_invFun h.inj x]

private theorem extFun_mul {i : A₀ →* A} {a : A} (h : IdxTwo i a) {j : B₀ →* B}
    {ψ : A₀ ≃* B₀} {b : B} (hb : b * b = 1)
    (hc : ∀ x x' : A₀, i x' = a * i x * a⁻¹ → j (ψ x') = b * j (ψ x) * b⁻¹) (x y : A) :
    extFun i j ψ a b (x * y) = extFun i j ψ a b x * extFun i j ψ a b y := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h.sq
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have dec : ∀ x : A, (∃ x₀, x = i x₀) ∨ (∃ x₀, x = i x₀ * a) := by
    intro x
    rcases h.cover x with ⟨x₀, hx₀⟩ | ⟨x₀, hx₀⟩
    · exact Or.inl ⟨x₀, hx₀.symm⟩
    · exact Or.inr ⟨x₀, by rw [hx₀, mul_assoc, h.sq, mul_one]⟩
  rcases dec x with ⟨x₀, rfl⟩ | ⟨x₀, rfl⟩ <;> rcases dec y with ⟨y₀, rfl⟩ | ⟨y₀, rfl⟩
  · have e : i x₀ * i y₀ = i (x₀ * y₀) := (map_mul i x₀ y₀).symm
    rw [e, extFun_i h.inj, extFun_i h.inj, extFun_i h.inj]
    simp only [map_mul]
  · have e : i x₀ * (i y₀ * a) = i (x₀ * y₀) * a := by rw [map_mul, mul_assoc]
    rw [e, extFun_i_mul h, extFun_i h.inj, extFun_i_mul h]
    simp only [map_mul, mul_assoc]
  · obtain ⟨y', hy'⟩ := h.exists_conj y₀
    have e : i x₀ * a * i y₀ = i (x₀ * y') * a := by rw [map_mul, hy']; group
    rw [e, extFun_i_mul h, extFun_i_mul h, extFun_i h.inj]
    simp only [map_mul]
    rw [hc y₀ y' hy']
    group
  · obtain ⟨y', hy'⟩ := h.exists_conj y₀
    have e : i x₀ * a * (i y₀ * a) = i (x₀ * y') := by rw [map_mul, hy', ha']; group
    rw [e, extFun_i h.inj, extFun_i_mul h, extFun_i_mul h]
    simp only [map_mul]
    rw [hc y₀ y' hy', hb']
    group

private noncomputable def extHom {i : A₀ →* A} {a : A} (h : IdxTwo i a) {j : B₀ →* B}
    {ψ : A₀ ≃* B₀} {b : B} (hb : b * b = 1)
    (hc : ∀ x x' : A₀, i x' = a * i x * a⁻¹ → j (ψ x') = b * j (ψ x) * b⁻¹) : A →* B where
  toFun := extFun i j ψ a b
  map_one' := by
    have := extFun_i (a := a) h.inj j ψ b 1
    simpa using this
  map_mul' := extFun_mul h hb hc

private theorem exists_mulEquiv_extend {i : A₀ →* A} {a : A} {j : B₀ →* B} {b : B}
    (hA : IdxTwo i a) (hB : IdxTwo j b) (ψ : A₀ ≃* B₀)
    (hc : ∀ x x' : A₀, i x' = a * i x * a⁻¹ → j (ψ x') = b * j (ψ x) * b⁻¹) :
    ∃ Ψ : A ≃* B, (∀ x, Ψ (i x) = j (ψ x)) ∧ Ψ a = b := by
  have hc' : ∀ y y' : B₀, j y' = b * j y * b⁻¹ →
      i (ψ.symm y') = a * i (ψ.symm y) * a⁻¹ := by
    intro y y' hy
    obtain ⟨x', hx'⟩ := hA.exists_conj (ψ.symm y)
    have h1 := hc (ψ.symm y) x' hx'
    rw [ψ.apply_symm_apply, ← hy] at h1
    have h2 : ψ x' = y' := hB.inj h1
    rw [← h2, ψ.symm_apply_apply]
    exact hx'
  let F : A →* B := extHom hA hB.sq hc
  let F' : B →* A := extHom hB hA.sq hc'
  have hF : ∀ x, F (i x) = j (ψ x) := fun x => extFun_i (a := a) hA.inj j ψ b x
  have hF' : ∀ y, F' (j y) = i (ψ.symm y) := fun y => extFun_i (a := b) hB.inj i ψ.symm a y
  have hFa : F a = b := by
    have h := extFun_i_mul hA j ψ b 1
    simp only [map_one, one_mul] at h
    exact h
  have hF'b : F' b = a := by
    have h := extFun_i_mul hB i ψ.symm a 1
    simp only [map_one, one_mul] at h
    exact h
  refine ⟨F.toMulEquiv F' ?_ ?_, hF, hFa⟩
  · refine hA.hom_ext (fun x => ?_) ?_
    · simp [hF, hF']
    · simp [hFa, hF'b]
  · refine hB.hom_ext (fun y => ?_) ?_
    · simp [hF, hF']
    · simp [hFa, hF'b]

end IndexTwo

section Sides

private def emb {Xh : Subgroup U42Aut.Ah} {X : Subgroup U42.Y}
    (hX : ∀ q : U42.Y, U42Aut.incl q ∈ Xh ↔ q ∈ X) : ↥X →* ↥Xh where
  toFun q := ⟨U42Aut.incl q, (hX q).2 q.2⟩
  map_one' := Subtype.ext (map_one U42Aut.incl)
  map_mul' a b := Subtype.ext (map_mul U42Aut.incl (a : U42.Y) (b : U42.Y))

private theorem idxTwo_emb {Xh : Subgroup U42Aut.Ah}
    {X : Subgroup U42.Y} (hX : ∀ q : U42.Y, U42Aut.incl q ∈ Xh ↔ q ∈ X) {f : U42Aut.Ah}
    (hfX : f ∈ Xh) (hfY : f ∉ U42Aut.Yh) (hf2 : f * f = 1) :
    IdxTwo (emb hX) (⟨f, hfX⟩ : ↥Xh) where
  inj q q' h := Subtype.ext (U42Aut.incl_injective (congrArg Subtype.val h))
  sq := Subtype.ext hf2
  notMem := by
    rintro ⟨q, hq⟩
    exact hfY ((U42Aut.mem_Yh_iff_incl f).2 ⟨q, congrArg Subtype.val hq⟩)
  cover p := by
    by_cases hp : (p : U42Aut.Ah) ∈ U42Aut.Yh
    · obtain ⟨y, hy⟩ := (U42Aut.mem_Yh_iff_incl _).1 hp
      refine Or.inl ⟨⟨y, (hX y).1 ?_⟩, Subtype.ext hy⟩
      rw [hy]
      exact p.2
    · have hs : U42Aut.signA ((p : U42Aut.Ah) * f) = 1 := by
        rw [map_mul, (U42Aut.signA_eq_neg_one_iff _).2 hp,
          (U42Aut.signA_eq_neg_one_iff f).2 hfY]
        decide
      obtain ⟨y, hy⟩ := (U42Aut.mem_Yh_iff_incl _).1 ((U42Aut.signA_eq_one_iff _).1 hs)
      refine Or.inr ⟨⟨y, (hX y).1 ?_⟩, Subtype.ext hy⟩
      rw [hy]
      exact Xh.mul_mem p.2 hfX

private theorem idxTwo_inclusion {G : Type*} [Group G] {B₀ Bg : Subgroup G} (hB : B₀ ≤ Bg)
    {τ : G} (hτ : τ ∈ Bg) (hτ' : τ ∉ B₀) (hττ : τ * τ = 1) (hidx : B₀.relIndex Bg = 2) :
    IdxTwo (Subgroup.inclusion hB) (⟨τ, hτ⟩ : ↥Bg) where
  inj := Subgroup.inclusion_injective hB
  sq := Subtype.ext hττ
  notMem := by
    rintro ⟨x, hx⟩
    have hxτ : (x : G) = τ := congrArg Subtype.val hx
    exact hτ' (hxτ ▸ x.2)
  cover y := by
    have h2 : (B₀.subgroupOf Bg).index = 2 := hidx
    by_cases hy : y ∈ B₀.subgroupOf Bg
    · exact Or.inl ⟨⟨(y : G), hy⟩, Subtype.ext rfl⟩
    · refine Or.inr ?_
      have hτK : (⟨τ, hτ⟩ : ↥Bg) ∉ B₀.subgroupOf Bg := hτ'
      obtain ⟨z, hz⟩ : ∃ z : ↥Bg, z = y * ⟨τ, hτ⟩ := ⟨_, rfl⟩
      have hmem : z ∈ B₀.subgroupOf Bg :=
        hz ▸ (Subgroup.mul_mem_iff_of_index_two h2).2 (iff_of_false hy hτK)
      exact ⟨⟨(z : G), hmem⟩, Subtype.ext (congrArg Subtype.val hz)⟩

variable {G : Type*} [Group G]

private theorem exists_equiv_of_tau {Xh : Subgroup U42Aut.Ah}
    {X : Subgroup U42.Y} (hX : ∀ q : U42.Y, U42Aut.incl q ∈ Xh ↔ q ∈ X) {f : U42Aut.Ah}
    (hfX : f ∈ Xh) (hfY : f ∉ U42Aut.Yh) (hf2 : f * f = 1) {Bg B₀ : Subgroup G} (hB : B₀ ≤ Bg)
    {τ : G} (hτ : τ ∈ Bg) (hτ' : τ ∉ B₀) (hττ : τ * τ = 1) (hn : ∀ m ∈ B₀, τ * m * τ⁻¹ ∈ B₀)
    (hidx : B₀.relIndex Bg = 2) (θ : ↥B₀ ≃* ↥X)
    (hθ : ∀ (m : G) (hm : m ∈ B₀) (hm' : τ * m * τ⁻¹ ∈ B₀),
      ((θ ⟨τ * m * τ⁻¹, hm'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
        (f : Equiv.Perm (Fin 45)) * ((θ ⟨m, hm⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
          (f : Equiv.Perm (Fin 45))⁻¹) :
    ∃ Ψ : ↥Xh ≃* ↥Bg, (∀ q : ↥X, (Ψ (emb hX q) : G) = (θ.symm q : G)) ∧
      (Ψ ⟨f, hfX⟩ : G) = τ := by
  have hcompat : ∀ q q' : ↥X, emb hX q' = (⟨f, hfX⟩ : ↥Xh) * emb hX q * (⟨f, hfX⟩ : ↥Xh)⁻¹ →
      Subgroup.inclusion hB (θ.symm q') = (⟨τ, hτ⟩ : ↥Bg) * Subgroup.inclusion hB (θ.symm q) *
        (⟨τ, hτ⟩ : ↥Bg)⁻¹ := by
    intro q q' hq
    obtain ⟨m, rfl⟩ := θ.surjective q
    obtain ⟨m', rfl⟩ := θ.surjective q'
    have e2 : ((θ m' : U42.Y) : Equiv.Perm (Fin 45)) =
        (f : Equiv.Perm (Fin 45)) * ((θ m : U42.Y) : Equiv.Perm (Fin 45)) *
          (f : Equiv.Perm (Fin 45))⁻¹ :=
      congrArg (fun p : ↥Xh => ((p : U42Aut.Ah) : Equiv.Perm (Fin 45))) hq
    have hm' : τ * (m : G) * τ⁻¹ ∈ B₀ := hn _ m.2
    have key := hθ (m : G) m.2 hm'
    have e3 : θ ⟨τ * (m : G) * τ⁻¹, hm'⟩ = θ m' := Subtype.ext (Subtype.ext (key.trans e2.symm))
    have e4 : (⟨τ * (m : G) * τ⁻¹, hm'⟩ : ↥B₀) = m' := θ.injective e3
    refine Subtype.ext ?_
    show ((θ.symm (θ m') : ↥B₀) : G) = τ * ((θ.symm (θ m) : ↥B₀) : G) * τ⁻¹
    rw [θ.symm_apply_apply, θ.symm_apply_apply]
    exact (congrArg Subtype.val e4).symm
  obtain ⟨Ψ, hΨ, hΨf⟩ := exists_mulEquiv_extend (idxTwo_emb hX hfX hfY hf2)
    (idxTwo_inclusion hB hτ hτ' hττ hidx) θ.symm hcompat
  exact ⟨Ψ, fun q => congrArg Subtype.val (hΨ q), congrArg Subtype.val hΨf⟩

end Sides

variable {G : Type} [Group G] [Finite G] {S : Setting G} {H : Subgroup G}

namespace ConfHyp

theorem autIso_of_tau (hc : ConfHyp S H)
    (h384 : Nat.card ↥(S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = 384)
    (h1920 : Nat.card (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = 1920)
    (M₀ : Subgroup G) (hM₀ : M₀ ≤ S.M) (hB : S.M ⊓ H ≤ M₀) (hidx : M₀.relIndex S.M = 2)
    (φ : (RankTwoAmalgam.ofSubgroups M₀ H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2))
    (hτ : ∃ τ : G, τ ∈ S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G) ∧
      τ ∉ M₀ ∧ τ * τ = 1 ∧ τ ∈ normalizer (M₀ : Set G) ∧ τ ∈ normalizer (H : Set G) ∧
      ∃ f : U42Aut.Ah, f ∈ U42Aut.Bh ∧ f ∉ U42Aut.Yh ∧ f * f = 1 ∧
        (∀ (m : G) (hm : m ∈ M₀) (hm' : τ * m * τ⁻¹ ∈ M₀),
          ((amPhi1 φ ⟨τ * m * τ⁻¹, hm'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
            (f : Equiv.Perm (Fin 45)) * ((amPhi1 φ ⟨m, hm⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
              (f : Equiv.Perm (Fin 45))⁻¹) ∧
        (∀ (h : G) (hh : h ∈ H) (hh' : τ * h * τ⁻¹ ∈ H),
          ((amPhi2 φ ⟨τ * h * τ⁻¹, hh'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
            (f : Equiv.Perm (Fin 45)) * ((amPhi2 φ ⟨h, hh⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
              (f : Equiv.Perm (Fin 45))⁻¹)) :
    Nonempty (U42Aut.AutIso S.M (normalizer ((closure (S.zConj H) : Subgroup G) : Set G))) := by
  obtain ⟨τ, hτMN, hτM₀, hττ, hτn₀, hτnH, f, hfB, hfY, hff, hcomp1, hcomp2⟩ := hτ
  have hHN : H ≤ normalizer ((closure (S.zConj H) : Subgroup G) : Set G) := hc.le_normalizer_V
  set N : Subgroup G := normalizer ((closure (S.zConj H) : Subgroup G) : Set G)
  have hτM : τ ∈ S.M := hτMN.1
  have hτN : τ ∈ N := hτMN.2
  have hτH : τ ∉ H := fun h => hτM₀ (hB ⟨hτM, h⟩)
  have hn₀ : ∀ m ∈ M₀, τ * m * τ⁻¹ ∈ M₀ := fun m hm => (mem_normalizer_iff.1 hτn₀ m).1 hm
  have hnH : ∀ m ∈ H, τ * m * τ⁻¹ ∈ H := fun m hm => (mem_normalizer_iff.1 hτnH m).1 hm
  have hn₁₂ : ∀ m ∈ M₀ ⊓ H, τ * m * τ⁻¹ ∈ M₀ ⊓ H := fun m hm => ⟨hn₀ m hm.1, hnH m hm.2⟩
  have hle₁₂ : M₀ ⊓ H ≤ S.M ⊓ N := inf_le_inf hM₀ hHN
  have hidx₂ : H.relIndex N = 2 := by
    have h1 := Setting.card_eq_relIndex_mul N H
    rw [inf_eq_right.mpr hHN, hc.card_H, h1920] at h1
    omega
  have hidx₁₂ : (M₀ ⊓ H).relIndex (S.M ⊓ N) = 2 := by
    have hMH : M₀ ⊓ H = S.M ⊓ H :=
      le_antisymm (inf_le_inf_right H hM₀) (le_inf hB inf_le_right)
    have hcard : Nat.card ↥(M₀ ⊓ H) = 192 := by rw [hMH]; exact hc.card_M_inf
    have h1 := Setting.card_eq_relIndex_mul (S.M ⊓ N) (M₀ ⊓ H)
    rw [inf_eq_right.mpr hle₁₂, hcard, h384] at h1
    omega
  have hX₁ : ∀ q : U42.Y, U42Aut.incl q ∈ U42Aut.P1h ↔ q ∈ U42.P1 :=
    fun q => SetLike.ext_iff.1 U42Aut.comap_P1h q
  have hX₂ : ∀ q : U42.Y, U42Aut.incl q ∈ U42Aut.P2h ↔ q ∈ U42.P2 :=
    fun q => SetLike.ext_iff.1 U42Aut.comap_P2h q
  have hX₁₂ : ∀ q : U42.Y, U42Aut.incl q ∈ U42Aut.P1h ⊓ U42Aut.P2h ↔ q ∈ U42.P1 ⊓ U42.P2 := by
    intro q
    rw [Subgroup.mem_inf, Subgroup.mem_inf, hX₁ q, hX₂ q]
  let θ₁₂ : ↥(M₀ ⊓ H) ≃* ↥(U42.P1 ⊓ U42.P2) := φ.φ12
  have hcomm1 : ∀ g : ↥(M₀ ⊓ H),
      (Subgroup.inclusion (inf_le_left : U42.P1 ⊓ U42.P2 ≤ U42.P1)) (θ₁₂ g) =
        amPhi1 φ (Subgroup.inclusion (inf_le_left : M₀ ⊓ H ≤ M₀) g) := φ.comm1
  have hcomm2 : ∀ g : ↥(M₀ ⊓ H),
      (Subgroup.inclusion (inf_le_right : U42.P1 ⊓ U42.P2 ≤ U42.P2)) (θ₁₂ g) =
        amPhi2 φ (Subgroup.inclusion (inf_le_right : M₀ ⊓ H ≤ H) g) := φ.comm2
  have hbr1 : ∀ g : ↥(M₀ ⊓ H),
      (((amPhi1 φ ⟨(g : G), g.2.1⟩ : ↥U42.P1) : U42.Y) : Equiv.Perm (Fin 45)) =
        (((θ₁₂ g : ↥(U42.P1 ⊓ U42.P2)) : U42.Y) : Equiv.Perm (Fin 45)) :=
    fun g => (congrArg (fun p : ↥U42.P1 => ((p : U42.Y) : Equiv.Perm (Fin 45))) (hcomm1 g)).symm
  have hcomp12 : ∀ (m : G) (hm : m ∈ M₀ ⊓ H) (hm' : τ * m * τ⁻¹ ∈ M₀ ⊓ H),
      (((θ₁₂ ⟨τ * m * τ⁻¹, hm'⟩ : ↥(U42.P1 ⊓ U42.P2)) : U42.Y) : Equiv.Perm (Fin 45)) =
        (f : Equiv.Perm (Fin 45)) *
          (((θ₁₂ ⟨m, hm⟩ : ↥(U42.P1 ⊓ U42.P2)) : U42.Y) : Equiv.Perm (Fin 45)) *
            (f : Equiv.Perm (Fin 45))⁻¹ := by
    intro m hm hm'
    calc (((θ₁₂ ⟨τ * m * τ⁻¹, hm'⟩ : ↥(U42.P1 ⊓ U42.P2)) : U42.Y) : Equiv.Perm (Fin 45))
        = (((amPhi1 φ ⟨τ * m * τ⁻¹, hm'.1⟩ : ↥U42.P1) : U42.Y) : Equiv.Perm (Fin 45)) :=
          (hbr1 ⟨τ * m * τ⁻¹, hm'⟩).symm
      _ = (f : Equiv.Perm (Fin 45)) *
          (((amPhi1 φ ⟨m, hm.1⟩ : ↥U42.P1) : U42.Y) : Equiv.Perm (Fin 45)) *
            (f : Equiv.Perm (Fin 45))⁻¹ := hcomp1 m hm.1 hm'.1
      _ = (f : Equiv.Perm (Fin 45)) *
          (((θ₁₂ ⟨m, hm⟩ : ↥(U42.P1 ⊓ U42.P2)) : U42.Y) : Equiv.Perm (Fin 45)) *
            (f : Equiv.Perm (Fin 45))⁻¹ := by rw [hbr1 ⟨m, hm⟩]
  obtain ⟨Ψ₁, hΨ₁, hΨ₁f⟩ := exists_equiv_of_tau hX₁ hfB.1 hfY hff hM₀ hτM hτM₀ hττ hn₀ hidx
    (amPhi1 φ) hcomp1
  obtain ⟨Ψ₂, hΨ₂, hΨ₂f⟩ := exists_equiv_of_tau hX₂ hfB.2 hfY hff hHN hτN hτH hττ hnH hidx₂
    (amPhi2 φ) hcomp2
  obtain ⟨Ψ₁₂, hΨ₁₂, hΨ₁₂f⟩ := exists_equiv_of_tau hX₁₂ hfB hfY hff hle₁₂ ⟨hτM, hτN⟩
    (fun h => hτM₀ h.1) hττ hn₁₂ hidx₁₂ θ₁₂ hcomp12
  have hbr₁ : ∀ q : ↥(U42.P1 ⊓ U42.P2),
      ((amPhi1 φ).symm ⟨(q : U42.Y), q.2.1⟩ : ↥M₀) =
        ⟨((θ₁₂.symm q : ↥(M₀ ⊓ H)) : G), (θ₁₂.symm q).2.1⟩ := by
    intro q
    rw [MulEquiv.symm_apply_eq]
    have h := hcomm1 (θ₁₂.symm q)
    rw [θ₁₂.apply_symm_apply] at h
    exact h
  have hbr₂ : ∀ q : ↥(U42.P1 ⊓ U42.P2),
      ((amPhi2 φ).symm ⟨(q : U42.Y), q.2.2⟩ : ↥H) =
        ⟨((θ₁₂.symm q : ↥(M₀ ⊓ H)) : G), (θ₁₂.symm q).2.2⟩ := by
    intro q
    rw [MulEquiv.symm_apply_eq]
    have h := hcomm2 (θ₁₂.symm q)
    rw [θ₁₂.apply_symm_apply] at h
    exact h
  refine ⟨{ φ1 := Ψ₁, φ12 := Ψ₁₂, φ2 := Ψ₂, comm1 := ?_, comm2 := ?_ }⟩
  · intro g
    have key : (Subgroup.inclusion (inf_le_left : S.M ⊓ N ≤ S.M)).comp Ψ₁₂.toMonoidHom =
        Ψ₁.toMonoidHom.comp
          (Subgroup.inclusion (inf_le_left : U42Aut.P1h ⊓ U42Aut.P2h ≤ U42Aut.P1h)) := by
      refine (idxTwo_emb hX₁₂ hfB hfY hff).hom_ext (fun q => ?_) ?_
      · refine Subtype.ext ?_
        exact (hΨ₁₂ q).trans ((congrArg Subtype.val (hbr₁ q)).symm.trans
          (hΨ₁ ⟨(q : U42.Y), q.2.1⟩).symm)
      · exact Subtype.ext (hΨ₁₂f.trans hΨ₁f.symm)
    exact DFunLike.congr_fun key g
  · intro g
    have key : (Subgroup.inclusion (inf_le_right : S.M ⊓ N ≤ N)).comp Ψ₁₂.toMonoidHom =
        Ψ₂.toMonoidHom.comp
          (Subgroup.inclusion (inf_le_right : U42Aut.P1h ⊓ U42Aut.P2h ≤ U42Aut.P2h)) := by
      refine (idxTwo_emb hX₁₂ hfB hfY hff).hom_ext (fun q => ?_) ?_
      · refine Subtype.ext ?_
        exact (hΨ₁₂ q).trans ((congrArg Subtype.val (hbr₂ q)).symm.trans
          (hΨ₂ ⟨(q : U42.Y), q.2.2⟩).symm)
      · exact Subtype.ext (hΨ₁₂f.trans hΨ₂f.symm)
    exact DFunLike.congr_fun key g

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
