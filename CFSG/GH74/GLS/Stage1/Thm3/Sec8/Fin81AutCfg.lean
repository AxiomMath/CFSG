module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Cfg
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Amalgam
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AutSL2
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81AutCoprime

public section

open Subgroup

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

section Toolbox

variable {A : Type*} [Group A] {F : Type} [Field F]

@[expose] def imgSL (K H : Subgroup A) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) :=
  (H.subgroupOf K).map e.toMonoidHom

theorem mem_imgSL {K H : Subgroup A} (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (y : Matrix.SpecialLinearGroup (Fin 2) F) : y ∈ imgSL K H e ↔ ((e.symm y : ↥K) : A) ∈ H := by
  unfold imgSL
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

theorem isSylowOf_imgSL [Finite F] (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {K H : Subgroup A}
    (hHK : H ≤ K) (hcard : Nat.card ↥H = 8) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    CFSG.ABGLocalTools.IsSylowOf 2 (imgSL K H e) ⊤ := by
  apply CFSG.ABGLocalTools.isSylowOf_of_card le_top
  rw [Subgroup.card_top, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    factorization_two_card_sl2 _ hmod]
  unfold imgSL
  rw [Subgroup.card_map_of_injective e.injective, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv,
    hcard]
  norm_num

@[expose] def imgEquiv {K H : Subgroup A} (hHK : H ≤ K) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ↥H ≃* ↥(imgSL K H e) :=
  (Subgroup.subgroupOfEquivOfLe hHK).symm.trans (e.subgroupMap (H.subgroupOf K))

end Toolbox

theorem FusedCfg.nonempty_equiv_q8 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {A : Type*} [Group A] {K₁ K₂ S : Subgroup A}
    (hc : FusedCfg K₁ K₂ S F) :
    Nonempty (↥(S ⊓ K₁) ≃* QuaternionGroup 2) ∧ Nonempty (↥(S ⊓ K₂) ≃* QuaternionGroup 2) := by
  have key : ∀ {K H : Subgroup A}, H ≤ K → Nat.card ↥H = 8 →
      ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F → Nonempty (↥H ≃* QuaternionGroup 2) := by
    intro K H hHK hcard e
    obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_isSylowOf (isSylowOf_imgSL hmod hHK hcard e)
    obtain ⟨φ⟩ := nonempty_equiv_q8_of_sylow hodd hmod Q
    exact ⟨(imgEquiv hHK e).trans ((MulEquiv.subgroupCongr hQ.symm).trans φ)⟩
  obtain ⟨e₁⟩ := hc.e₁
  obtain ⟨e₂⟩ := hc.e₂
  exact ⟨key inf_le_right hc.card₁ e₁, key inf_le_right hc.card₂ e₂⟩

section PartA

@[expose] def restrictAut {M : Type*} [Group M] (Q : Subgroup M) (α : MulAut M)
    (h : ∀ x, x ∈ Q ↔ α x ∈ Q) : MulAut ↥Q where
  toFun x := ⟨α x, (h x).mp x.2⟩
  invFun y := ⟨α.symm y, by rw [h]; simp⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp

theorem restrictAut_pow_apply {M : Type*} [Group M] (Q : Subgroup M) (α : MulAut M)
    (h : ∀ x, x ∈ Q ↔ α x ∈ Q) (n : ℕ) (x : ↥Q) :
    ((((restrictAut Q α h) ^ n) x : ↥Q) : M) = (α ^ n) (x : M) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem comm_of_comm_imgSL {A : Type*} [Group A] {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {K H : Subgroup A}
    (hHK : H ≤ K) (hcard : Nat.card ↥H = 8) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (x : ↥K)
    (hx : ∀ y ∈ H, (x : A) * y = y * (x : A)) : ∀ y : ↥K, x * y = y * x := by
  have hP := isSylowOf_imgSL hmod hHK hcard e
  have hz := centralizer_sylow_le_center hodd h5 hmod hP (x := e x) (by
    intro y hy
    have hy' : ((e.symm y : ↥K) : A) ∈ H := (mem_imgSL e y).1 hy
    have h2 : x * e.symm y = e.symm y * x := Subtype.ext (hx _ hy')
    have := congrArg e h2
    simpa using this)
  intro y
  have := Subgroup.mem_center_iff.1 hz (e y)
  apply e.injective
  simpa using this.symm

theorem aut_mem_of_fixing {A : Type*} [Group A] {M K₁ K₂ P₂ : Subgroup A}
    (hdec : ∀ m ∈ M, ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = m) (hM₂ : K₂ ≤ M) (hP₂ : P₂ ≤ K₂)
    (hcomm : ∀ a ∈ K₁, ∀ b ∈ K₂, a * b = b * a)
    (hcen : ∀ b ∈ K₂, (∀ y ∈ P₂, b * y = y * b) → b ∈ K₁)
    (ρ : MulAut ↥M) (hfix : ∀ y : ↥M, (y : A) ∈ P₂ → ρ y = y)
    (k : ↥M) (hk : (k : A) ∈ K₁) : ((ρ k : ↥M) : A) ∈ K₁ := by
  obtain ⟨a, ha, b, hb, hab⟩ := hdec (ρ k) (ρ k).2
  have hcb : ∀ y ∈ P₂, Commute b y := by
    intro y hy
    have hyM : y ∈ M := hM₂ (hP₂ hy)
    have h2 : Commute ((ρ k : ↥M) : A) y := by
      have h1 : k * ⟨y, hyM⟩ = ⟨y, hyM⟩ * k := Subtype.ext (hcomm _ hk y (hP₂ hy))
      have := congrArg ρ h1
      rw [map_mul, map_mul, hfix ⟨y, hyM⟩ hy] at this
      exact congrArg Subtype.val this
    have h3 : Commute a y := hcomm a ha y (hP₂ hy)
    have hb' : b = a⁻¹ * ((ρ k : ↥M) : A) := by rw [← hab]; group
    rw [hb']
    exact (h3.inv_left).mul_left h2
  have hb1 : b ∈ K₁ := hcen b hb (fun y hy => (hcb y hy).eq)
  rw [← hab]
  exact K₁.mul_mem ha hb1

theorem odd_orderOf_restrict {A : Type*} [Group A] {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) {M K H : Subgroup A}
    (hKM : K ≤ M) (hHK : H ≤ K) (hcard : Nat.card ↥H = 8) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (ρ : MulAut ↥M) (hρ : ∀ x : ↥M, (x : A) ∈ K ↔ ((ρ x : ↥M) : A) ∈ K)
    (hfix : ∀ y : ↥M, (y : A) ∈ H → ρ y = y) :
    Odd (orderOf (restrictAut (K.subgroupOf M) ρ (fun x => hρ x))) := by
  set σ := restrictAut (K.subgroupOf M) ρ (fun x => hρ x) with hσ
  let E : ↥(K.subgroupOf M) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (Subgroup.subgroupOfEquivOfLe hKM).trans e
  have hP := isSylowOf_imgSL hmod hHK hcard e
  have hfixγ : ∀ x ∈ imgSL K H e, (MulAut.congr E σ) x = x := by
    intro x hx
    have hxH : ((e.symm x : ↥K) : A) ∈ H := (mem_imgSL e x).1 hx
    change E (σ (E.symm x)) = x
    have hq : σ (E.symm x) = E.symm x := by
      apply Subtype.ext
      exact hfix ((E.symm x : ↥(K.subgroupOf M)) : ↥M) hxH
    rw [hq]
    exact E.apply_symm_apply x
  have hodd' := odd_orderOf_of_fixing_sylow hodd h5 hmod hP (MulAut.congr E σ) hfixγ
  rwa [MulEquiv.orderOf_eq] at hodd'

theorem odd_orderOf_of_restrictions {M : Type*} [Group M] {Q₁ Q₂ : Subgroup M} (hQ : Q₁ ⊔ Q₂ = ⊤)
    (ρ : MulAut M) (h₁ : ∀ x, x ∈ Q₁ ↔ ρ x ∈ Q₁) (h₂ : ∀ x, x ∈ Q₂ ↔ ρ x ∈ Q₂)
    (o₁ : Odd (orderOf (restrictAut Q₁ ρ h₁))) (o₂ : Odd (orderOf (restrictAut Q₂ ρ h₂))) :
    Odd (orderOf ρ) := by
  have hfixpow : ∀ (g : MulAut M) (x : M), g x = x → ∀ n : ℕ, (g ^ n) x = x := by
    intro g x hx n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]
  have hfix1 : ∀ x ∈ Q₁, (ρ ^ orderOf (restrictAut Q₁ ρ h₁)) x = x := by
    intro x hx
    have := restrictAut_pow_apply Q₁ ρ h₁ (orderOf (restrictAut Q₁ ρ h₁)) ⟨x, hx⟩
    rw [pow_orderOf_eq_one] at this
    exact this.symm
  have hfix2 : ∀ x ∈ Q₂, (ρ ^ orderOf (restrictAut Q₂ ρ h₂)) x = x := by
    intro x hx
    have := restrictAut_pow_apply Q₂ ρ h₂ (orderOf (restrictAut Q₂ ρ h₂)) ⟨x, hx⟩
    rw [pow_orderOf_eq_one] at this
    exact this.symm
  have hone : ρ ^ (orderOf (restrictAut Q₁ ρ h₁) * orderOf (restrictAut Q₂ ρ h₂)) = 1 := by
    let E : Subgroup M := MonoidHom.eqLocus
      (ρ ^ (orderOf (restrictAut Q₁ ρ h₁) * orderOf (restrictAut Q₂ ρ h₂))).toMonoidHom (MonoidHom.id M)
    have hQ₁ : Q₁ ≤ E := by
      intro x hx
      show (ρ ^ (orderOf (restrictAut Q₁ ρ h₁) * orderOf (restrictAut Q₂ ρ h₂))) x = x
      rw [pow_mul]
      exact hfixpow _ x (hfix1 x hx) _
    have hQ₂ : Q₂ ≤ E := by
      intro x hx
      show (ρ ^ (orderOf (restrictAut Q₁ ρ h₁) * orderOf (restrictAut Q₂ ρ h₂))) x = x
      rw [mul_comm, pow_mul]
      exact hfixpow _ x (hfix2 x hx) _
    have htop : (⊤ : Subgroup M) ≤ E := hQ ▸ sup_le hQ₁ hQ₂
    apply MulEquiv.ext
    intro x
    exact htop (Subgroup.mem_top x)
  exact Odd.of_dvd_nat (o₁.mul o₂) (orderOf_dvd_of_pow_eq_one hone)

theorem odd_orderOf_of_fixing_cfg {A : Type*} [Group A] [Finite A] {F : Type} [Field F] [Finite F]
    {K₁ K₂ S : Subgroup A} (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (hc : FusedCfg K₁ K₂ S F)
    (ρ : MulAut ↥(K₁ ⊔ K₂)) (hfix : ∀ x : ↥(K₁ ⊔ K₂), (x : A) ∈ S → ρ x = x) :
    Odd (orderOf ρ) := by
  obtain ⟨e₁⟩ := hc.e₁
  obtain ⟨e₂⟩ := hc.e₂
  have hfix' : ∀ x : ↥(K₁ ⊔ K₂), (x : A) ∈ S → ρ⁻¹ x = x :=
    fun x hx => ρ.symm_apply_eq.2 (hfix x hx).symm
  have hdec₁ : ∀ m ∈ K₁ ⊔ K₂, ∃ a ∈ K₁, ∃ b ∈ K₂, a * b = m := by
    intro m hm
    obtain ⟨a, b, h⟩ := mem_sup_of_commute_aux hc.comm hm
    exact ⟨a, a.2, b, b.2, h⟩
  have hdec₂ : ∀ m ∈ K₁ ⊔ K₂, ∃ a ∈ K₂, ∃ b ∈ K₁, a * b = m := by
    intro m hm
    obtain ⟨a, b, h⟩ := mem_sup_of_commute_aux hc.comm hm
    exact ⟨b, b.2, a, a.2, by rw [← h]; exact (hc.comm a a.2 b b.2).symm⟩
  have hcen₂ : ∀ b ∈ K₂, (∀ y ∈ S ⊓ K₂, b * y = y * b) → b ∈ K₁ := by
    intro b hb hy
    have := comm_of_comm_imgSL hodd h5 hmod (inf_le_right : S ⊓ K₂ ≤ K₂) hc.card₂ e₂ ⟨b, hb⟩ hy
    exact hc.cen₂ b hb (fun y hy' => congrArg Subtype.val (this ⟨y, hy'⟩))
  have hcen₁ : ∀ a ∈ K₁, (∀ y ∈ S ⊓ K₁, a * y = y * a) → a ∈ K₂ := by
    intro a ha hy
    have := comm_of_comm_imgSL hodd h5 hmod (inf_le_right : S ⊓ K₁ ≤ K₁) hc.card₁ e₁ ⟨a, ha⟩ hy
    exact hc.cen₁ a ha (fun y hy' => congrArg Subtype.val (this ⟨y, hy'⟩))
  have pres₁ : ∀ ρ' : MulAut ↥(K₁ ⊔ K₂), (∀ x : ↥(K₁ ⊔ K₂), (x : A) ∈ S → ρ' x = x) →
      ∀ k : ↥(K₁ ⊔ K₂), (k : A) ∈ K₁ → ((ρ' k : ↥(K₁ ⊔ K₂)) : A) ∈ K₁ :=
    fun ρ' hf k hk => aut_mem_of_fixing (P₂ := S ⊓ K₂) hdec₁ le_sup_right inf_le_right hc.comm hcen₂ ρ'
      (fun y hy => hf y hy.1) k hk
  have pres₂ : ∀ ρ' : MulAut ↥(K₁ ⊔ K₂), (∀ x : ↥(K₁ ⊔ K₂), (x : A) ∈ S → ρ' x = x) →
      ∀ k : ↥(K₁ ⊔ K₂), (k : A) ∈ K₂ → ((ρ' k : ↥(K₁ ⊔ K₂)) : A) ∈ K₂ :=
    fun ρ' hf k hk => aut_mem_of_fixing (K₁ := K₂) (K₂ := K₁) (P₂ := S ⊓ K₁) hdec₂ le_sup_left inf_le_right
      (fun a ha b hb => (hc.comm b hb a ha).symm) hcen₁ ρ' (fun y hy => hf y hy.1) k hk
  have h₁ : ∀ x : ↥(K₁ ⊔ K₂), (x : A) ∈ K₁ ↔ ((ρ x : ↥(K₁ ⊔ K₂)) : A) ∈ K₁ := by
    intro x
    refine ⟨pres₁ ρ hfix x, fun h => ?_⟩
    have := pres₁ ρ⁻¹ hfix' (ρ x) h
    simpa using this
  have h₂ : ∀ x : ↥(K₁ ⊔ K₂), (x : A) ∈ K₂ ↔ ((ρ x : ↥(K₁ ⊔ K₂)) : A) ∈ K₂ := by
    intro x
    refine ⟨pres₂ ρ hfix x, fun h => ?_⟩
    have := pres₂ ρ⁻¹ hfix' (ρ x) h
    simpa using this
  have o₁ := odd_orderOf_restrict hodd h5 hmod (le_sup_left : K₁ ≤ K₁ ⊔ K₂) (inf_le_right : S ⊓ K₁ ≤ K₁)
    hc.card₁ e₁ ρ h₁ (fun y hy => hfix y hy.1)
  have o₂ := odd_orderOf_restrict hodd h5 hmod (le_sup_right : K₂ ≤ K₁ ⊔ K₂) (inf_le_right : S ⊓ K₂ ≤ K₂)
    hc.card₂ e₂ ρ h₂ (fun y hy => hfix y hy.1)
  have hQ : (K₁.subgroupOf (K₁ ⊔ K₂)) ⊔ (K₂.subgroupOf (K₁ ⊔ K₂)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self _
  exact odd_orderOf_of_restrictions hQ ρ (fun x => h₁ x) (fun x => h₂ x) o₁ o₂

end PartA

section PartB

@[expose] def restrictInf {A A' : Type*} [Group A] [Group A'] {S L : Subgroup A} {S' L' : Subgroup A'}
    (α : ↥S ≃* ↥S') (h : ∀ x : ↥S, (x : A) ∈ L ↔ ((α x : ↥S') : A') ∈ L') :
    ↥(S ⊓ L) ≃* ↥(S' ⊓ L') where
  toFun x := ⟨((α ⟨x.1, x.2.1⟩ : ↥S') : A'), (α ⟨x.1, x.2.1⟩).2, (h ⟨x.1, x.2.1⟩).1 x.2.2⟩
  invFun y := ⟨((α.symm ⟨y.1, y.2.1⟩ : ↥S) : A), (α.symm ⟨y.1, y.2.1⟩).2,
    (h (α.symm ⟨y.1, y.2.1⟩)).2 (by rw [α.apply_symm_apply]; exact y.2.2)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by
    apply Subtype.ext
    have h1 : (⟨((x * y : ↥(S ⊓ L)) : A), (x * y).2.1⟩ : ↥S) = ⟨x.1, x.2.1⟩ * ⟨y.1, y.2.1⟩ := rfl
    show ((α ⟨((x * y : ↥(S ⊓ L)) : A), (x * y).2.1⟩ : ↥S') : A') = _
    rw [h1, map_mul]
    rfl

theorem exists_equiv_extending {A A' : Type*} [Group A] [Group A'] {F : Type} [Field F] [Finite F]
    (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    {K H : Subgroup A} {K' H' : Subgroup A'} (hHK : H ≤ K) (hHK' : H' ≤ K') (hH : Nat.card ↥H = 8)
    (hH' : Nat.card ↥H' = 8) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (e' : ↥K' ≃* Matrix.SpecialLinearGroup (Fin 2) F) (β : ↥H ≃* ↥H') :
    ∃ φ : ↥K ≃* ↥K', ∀ (x : A) (hx : x ∈ H),
      ((φ ⟨x, hHK hx⟩ : ↥K') : A') = ((β ⟨x, hx⟩ : ↥H') : A') := by
  have hP := isSylowOf_imgSL hmod hHK hH e
  have hP' := isSylowOf_imgSL hmod hHK' hH' e'
  let ψ : ↥(imgSL K H e) ≃* ↥(imgSL K' H' e') :=
    (imgEquiv hHK e).symm.trans (β.trans (imgEquiv hHK' e'))
  obtain ⟨γ, hγ⟩ := exists_aut_extending_sylow hodd h5 hmod hP hP' ψ
  refine ⟨e.trans (γ.trans e'.symm), fun x hx => ?_⟩
  have h1 : γ (e ⟨x, hHK hx⟩) = ((ψ (imgEquiv hHK e ⟨x, hx⟩) : ↥(imgSL K' H' e')) :
      Matrix.SpecialLinearGroup (Fin 2) F) := hγ (imgEquiv hHK e ⟨x, hx⟩)
  have h2 : ψ (imgEquiv hHK e ⟨x, hx⟩) = imgEquiv hHK' e' (β ⟨x, hx⟩) := by simp [ψ]
  change ((e'.symm (γ (e ⟨x, hHK hx⟩)) : ↥K') : A') = _
  rw [h1, h2]
  change ((e'.symm (e' ⟨((β ⟨x, hx⟩ : ↥H') : A'), hHK' (β ⟨x, hx⟩).2⟩) : ↥K') : A') = _
  rw [e'.symm_apply_apply]

theorem FusedCfg.inf_le_S {A : Type*} [Group A] {F : Type} [Field F] {K₁ K₂ S : Subgroup A}
    (hc : FusedCfg K₁ K₂ S F) : K₁ ⊓ K₂ ≤ S := by
  obtain ⟨z, hz, ho, hzS, -⟩ := hc.z_ex
  have hle : Subgroup.zpowers z ≤ K₁ ⊓ K₂ := (Subgroup.zpowers_le).2 hz
  have : Finite ↥(K₁ ⊓ K₂) := Nat.finite_of_card_ne_zero (by rw [hc.card_inf]; norm_num)
  have hcard : Nat.card ↥(K₁ ⊓ K₂) ≤ Nat.card ↥(Subgroup.zpowers z) := by
    rw [hc.card_inf, Nat.card_zpowers, ho]
  have heq : Subgroup.zpowers z = K₁ ⊓ K₂ := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq]
  exact (Subgroup.zpowers_le).2 hzS

theorem exists_phi_extending {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A'] {F : Type} [Field F]
    [Finite F] {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'} (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (hc : FusedCfg K₁ K₂ S F) (hc' : FusedCfg K₁' K₂' S' F) (α : ↥S ≃* ↥S')
    (h₁ : ∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₁')
    (h₂ : ∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₂') :
    ∃ φ : ↥(K₁ ⊔ K₂) ≃* ↥(K₁' ⊔ K₂'), ∀ (x : ↥S) (hx : (x : A) ∈ K₁ ⊔ K₂),
      ((φ ⟨(x : A), hx⟩ : ↥(K₁' ⊔ K₂')) : A') = ((α x : ↥S') : A') := by
  obtain ⟨e₁⟩ := hc.e₁
  obtain ⟨e₂⟩ := hc.e₂
  obtain ⟨e₁'⟩ := hc'.e₁
  obtain ⟨e₂'⟩ := hc'.e₂
  obtain ⟨φ₁, hφ₁⟩ := exists_equiv_extending hodd h5 hmod (inf_le_right : S ⊓ K₁ ≤ K₁)
    (inf_le_right : S' ⊓ K₁' ≤ K₁') hc.card₁ hc'.card₁ e₁ e₁' (restrictInf α h₁)
  obtain ⟨φ₂, hφ₂⟩ := exists_equiv_extending hodd h5 hmod (inf_le_right : S ⊓ K₂ ≤ K₂)
    (inf_le_right : S' ⊓ K₂' ≤ K₂') hc.card₂ hc'.card₂ e₂ e₂' (restrictInf α h₂)
  have hφ₁' : ∀ (x : A) (hxS : x ∈ S) (hx₁ : x ∈ K₁),
      ((φ₁ ⟨x, hx₁⟩ : ↥K₁') : A') = ((α ⟨x, hxS⟩ : ↥S') : A') := fun x hxS hx₁ =>
    hφ₁ x ⟨hxS, hx₁⟩
  have hφ₂' : ∀ (x : A) (hxS : x ∈ S) (hx₂ : x ∈ K₂),
      ((φ₂ ⟨x, hx₂⟩ : ↥K₂') : A') = ((α ⟨x, hxS⟩ : ↥S') : A') := fun x hxS hx₂ =>
    hφ₂ x ⟨hxS, hx₂⟩
  have hKS := hc.inf_le_S
  have hZ : ∀ (a : ↥K₁) (b : ↥K₂), (a : A) = (b : A) → ((φ₁ a : ↥K₁') : A') = ((φ₂ b : ↥K₂') : A') := by
    intro a b hab
    have haS : (a : A) ∈ S := hKS ⟨a.2, hab ▸ b.2⟩
    have hbS : (b : A) ∈ S := hab ▸ haS
    have h1 := hφ₁' (a : A) haS a.2
    have h2 := hφ₂' (b : A) hbS b.2
    have h3 : (⟨(a : A), haS⟩ : ↥S) = ⟨(b : A), hbS⟩ := Subtype.ext hab
    rw [h1, h2, h3]
  have hZ' : ∀ (a : ↥K₁) (b : ↥K₂), ((φ₁ a : ↥K₁') : A') = ((φ₂ b : ↥K₂') : A') → (a : A) = (b : A) := by
    intro a b hab
    have ha₂ : (a : A) ∈ K₂ := by
      apply hc.cen₁ _ a.2
      intro y hy
      have hcomm : ∀ y' : ↥K₁', ((φ₁ a : ↥K₁') : A') * (y' : A') = (y' : A') * ((φ₁ a : ↥K₁') : A') := by
        intro y'
        rw [hab]
        exact (hc'.comm _ y'.2 _ (φ₂ b).2).symm
      have h2 := hcomm (φ₁ ⟨y, hy⟩)
      have h3 : φ₁ a * φ₁ ⟨y, hy⟩ = φ₁ ⟨y, hy⟩ * φ₁ a := Subtype.ext h2
      rw [← map_mul, ← map_mul] at h3
      exact congrArg Subtype.val (φ₁.injective h3)
    have hb₁ : (b : A) ∈ K₁ := by
      apply hc.cen₂ _ b.2
      intro y hy
      have hcomm : ∀ y' : ↥K₂', ((φ₂ b : ↥K₂') : A') * (y' : A') = (y' : A') * ((φ₂ b : ↥K₂') : A') := by
        intro y'
        rw [← hab]
        exact hc'.comm _ (φ₁ a).2 _ y'.2
      have h2 := hcomm (φ₂ ⟨y, hy⟩)
      have h3 : φ₂ b * φ₂ ⟨y, hy⟩ = φ₂ ⟨y, hy⟩ * φ₂ b := Subtype.ext h2
      rw [← map_mul, ← map_mul] at h3
      exact congrArg Subtype.val (φ₂.injective h3)
    have haS : (a : A) ∈ S := hKS ⟨a.2, ha₂⟩
    have hbS : (b : A) ∈ S := hKS ⟨hb₁, b.2⟩
    have h1 := hφ₁' (a : A) haS a.2
    have h2 := hφ₂' (b : A) hbS b.2
    rw [h1, h2] at hab
    have h3 : (⟨(a : A), haS⟩ : ↥S) = ⟨(b : A), hbS⟩ := α.injective (Subtype.ext hab)
    exact congrArg Subtype.val h3
  obtain ⟨φ, hφa, hφb⟩ := centralProduct_mulEquiv K₁ K₂ K₁' K₂' hc.comm hc'.comm φ₁ φ₂ hZ hZ'
  refine ⟨φ, fun x hx => ?_⟩
  have hxprod : (x : A) ∈ (S ⊓ K₁) ⊔ (S ⊓ K₂) := by
    rw [← hc.prod]
    exact ⟨x.2, hx⟩
  obtain ⟨a, b, hab⟩ := mem_sup_of_commute_aux (A₁ := S ⊓ K₁) (A₂ := S ⊓ K₂)
    (fun a ha b hb => hc.comm a ha.2 b hb.2) hxprod
  have e1 : (⟨(x : A), hx⟩ : ↥(K₁ ⊔ K₂)) =
      ⟨(a : A), Subgroup.mem_sup_left a.2.2⟩ * ⟨(b : A), Subgroup.mem_sup_right b.2.2⟩ := Subtype.ext hab.symm
  have e2 : x = ⟨(a : A), a.2.1⟩ * ⟨(b : A), b.2.1⟩ := Subtype.ext hab.symm
  rw [e1, map_mul, Subgroup.coe_mul, hφa ⟨(a : A), a.2.2⟩, hφb ⟨(b : A), b.2.2⟩, hφ₁' _ a.2.1 a.2.2,
    hφ₂' _ b.2.1 b.2.2, e2, map_mul]
  rfl

end PartB

section PartC

theorem alpha_mem_sup {A A' : Type*} [Group A] [Group A'] {F : Type} [Field F]
    {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'} (hc : FusedCfg K₁ K₂ S F) (α : ↥S ≃* ↥S')
    (h₁ : ∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₁')
    (h₂ : ∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₂')
    (x : ↥S) (hx : (x : A) ∈ K₁ ⊔ K₂) : ((α x : ↥S') : A') ∈ K₁' ⊔ K₂' := by
  have hxprod : (x : A) ∈ (S ⊓ K₁) ⊔ (S ⊓ K₂) := by
    rw [← hc.prod]
    exact ⟨x.2, hx⟩
  obtain ⟨a, b, hab⟩ := mem_sup_of_commute_aux (A₁ := S ⊓ K₁) (A₂ := S ⊓ K₂)
    (fun a ha b hb => hc.comm a ha.2 b hb.2) hxprod
  have e2 : x = ⟨(a : A), a.2.1⟩ * ⟨(b : A), b.2.1⟩ := Subtype.ext hab.symm
  rw [e2, map_mul, Subgroup.coe_mul]
  exact Subgroup.mul_mem_sup ((h₁ ⟨(a : A), a.2.1⟩).1 a.2.2) ((h₂ ⟨(b : A), b.2.1⟩).1 b.2.2)

theorem alpha_mem_sup_iff {A A' : Type*} [Group A] [Group A'] {F : Type} [Field F]
    {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'} (hc : FusedCfg K₁ K₂ S F)
    (hc' : FusedCfg K₁' K₂' S' F) (α : ↥S ≃* ↥S')
    (h₁ : ∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₁')
    (h₂ : ∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₂')
    (x : ↥S) : (x : A) ∈ K₁ ⊔ K₂ ↔ ((α x : ↥S') : A') ∈ K₁' ⊔ K₂' := by
  refine ⟨alpha_mem_sup hc α h₁ h₂ x, fun hx => ?_⟩
  have := alpha_mem_sup hc' α.symm (fun y => by simpa using (h₁ (α.symm y)).symm)
    (fun y => by simpa using (h₂ (α.symm y)).symm) (α x) hx
  simpa using this

@[expose] def conjAct {X : Type*} [Group X] (K T : Subgroup X) (hT : T ≤ normalizer (K : Set X)) :
    ↥T →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (MonoidHom.codRestrict T.subtype _ (fun t => hT t.2))

theorem coe_conjAct {X : Type*} [Group X] (K T : Subgroup X) (hT : T ≤ normalizer (K : Set X)) (t : ↥T)
    (k : ↥K) : ((conjAct K T hT t k : ↥K) : X) = (t : X) * (k : X) * (t : X)⁻¹ := by
  simp [conjAct]

@[expose] def fixS {X : Type*} [Group X] (K' S' : Subgroup X) : Subgroup (MulAut ↥K') where
  carrier := {ρ | ∀ x : ↥K', (x : X) ∈ S' → ρ x = x}
  mul_mem' := by
    intro a b ha hb x hx
    rw [MulAut.mul_apply, hb x hx, ha x hx]
  one_mem' := by
    intro x _
    rfl
  inv_mem' := by
    intro a ha x hx
    exact a.symm_apply_eq.2 (ha x hx).symm

theorem odd_card_fixS {A' : Type*} [Group A'] [Finite A'] {F : Type} [Field F] [Finite F]
    {K₁' K₂' S' : Subgroup A'} (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5) (hc' : FusedCfg K₁' K₂' S' F) :
    Odd (Nat.card ↥(fixS (K₁' ⊔ K₂') S')) := by
  by_contra hne
  have hev : 2 ∣ Nat.card ↥(fixS (K₁' ⊔ K₂') S') :=
    even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hev
  have hodd' := odd_orderOf_of_fixing_cfg hodd h5 hmod hc' (x : MulAut ↥(K₁' ⊔ K₂')) x.2
  rw [Subgroup.orderOf_coe, hx] at hodd'
  exact (Nat.not_even_iff_odd.2 hodd') even_two

theorem exists_phi_intertwining {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A'] {F : Type}
    [Field F] [Finite F] {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'} (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (hc : FusedCfg K₁ K₂ S F) (hc' : FusedCfg K₁' K₂' S' F) (α : ↥S ≃* ↥S')
    (h₁ : ∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₁')
    (h₂ : ∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₂') :
    ∃ φ : ↥(K₁ ⊔ K₂) ≃* ↥(K₁' ⊔ K₂'),
      (∀ (x : ↥S) (hx : (x : A) ∈ K₁ ⊔ K₂),
        ((φ ⟨(x : A), hx⟩ : ↥(K₁' ⊔ K₂')) : A') = ((α x : ↥S') : A')) ∧
      (∀ (s : ↥S) (k : ↥(K₁ ⊔ K₂)) (hk : (s : A) * (k : A) * (s : A)⁻¹ ∈ K₁ ⊔ K₂),
        ((φ ⟨(s : A) * (k : A) * (s : A)⁻¹, hk⟩ : ↥(K₁' ⊔ K₂')) : A') =
          ((α s : ↥S') : A') * ((φ k : ↥(K₁' ⊔ K₂')) : A') * ((α s : ↥S') : A')⁻¹) ∧
      (∀ k : ↥(K₁ ⊔ K₂), ((φ k : ↥(K₁' ⊔ K₂')) : A') ∈ S' → (k : A) ∈ S) := by
  obtain ⟨φ, hφ⟩ := exists_phi_extending hodd h5 hmod hc hc' α h₁ h₂
  have hα := alpha_mem_sup_iff hc hc' α h₁ h₂
  let cS : ↥S →* MulAut ↥(K₁' ⊔ K₂') := (conjAct (K₁' ⊔ K₂') S' hc'.norm).comp α.toMonoidHom
  let Θ : ↥S →* MulAut ↥(K₁' ⊔ K₂') :=
    (MulAut.congr φ).toMonoidHom.comp (conjAct (K₁ ⊔ K₂) S hc.norm)
  have hcS : ∀ (s : ↥S) (k : ↥(K₁' ⊔ K₂')), ((cS s k : ↥(K₁' ⊔ K₂')) : A') =
      ((α s : ↥S') : A') * (k : A') * ((α s : ↥S') : A')⁻¹ := fun s k => coe_conjAct (K₁' ⊔ K₂') S' hc'.norm (α s) k
  have hinv : ∀ (s : ↥S) (x : ↥(K₁' ⊔ K₂')), (x : A') ∈ S' →
      (((cS s)⁻¹ x : ↥(K₁' ⊔ K₂')) : A') = ((α s : ↥S') : A')⁻¹ * (x : A') * ((α s : ↥S') : A') := by
    intro s x hx
    have h1 : cS s⁻¹ x = (cS s)⁻¹ x := by rw [map_inv]
    rw [← h1, hcS]
    simp
  have hinvS : ∀ (s : ↥S) (x : ↥(K₁' ⊔ K₂')), (x : A') ∈ S' → (((cS s)⁻¹ x : ↥(K₁' ⊔ K₂')) : A') ∈ S' := by
    intro s x hx
    rw [hinv s x hx]
    exact S'.mul_mem (S'.mul_mem (S'.inv_mem (α s).2) hx) (α s).2
  have hsurj : ∀ y : ↥(K₁' ⊔ K₂'), (y : A') ∈ S' →
      ∃ (w : ↥S) (hw : (w : A) ∈ K₁ ⊔ K₂), φ ⟨(w : A), hw⟩ = y := by
    intro y hy
    have hw : ((α.symm ⟨(y : A'), hy⟩ : ↥S) : A) ∈ K₁ ⊔ K₂ := by
      rw [hα]
      simp
    refine ⟨α.symm ⟨(y : A'), hy⟩, hw, ?_⟩
    apply Subtype.ext
    rw [hφ _ hw]
    simp
  have hdiff : ∀ s : ↥S, Θ s * (cS s)⁻¹ ∈ fixS (K₁' ⊔ K₂') S' := by
    intro s x hx
    set y := (cS s)⁻¹ x with hy
    have hyS : (y : A') ∈ S' := hinvS s x hx
    obtain ⟨w, hw, hwy⟩ := hsurj y hyS
    have hφinv : φ.symm y = ⟨(w : A), hw⟩ := by rw [← hwy]; exact φ.symm_apply_apply _
    rw [MulAut.mul_apply]
    show Θ s y = x
    have hΘ : Θ s y = φ (conjAct (K₁ ⊔ K₂) S hc.norm s (φ.symm y)) := rfl
    rw [hΘ, hφinv]
    have hk₂ : ((conjAct (K₁ ⊔ K₂) S hc.norm s ⟨(w : A), hw⟩ : ↥(K₁ ⊔ K₂)) : A) =
        ((s * w * s⁻¹ : ↥S) : A) := by
      rw [coe_conjAct]
      simp
    have hk₃ : ((s * w * s⁻¹ : ↥S) : A) ∈ K₁ ⊔ K₂ := hk₂ ▸ (conjAct (K₁ ⊔ K₂) S hc.norm s ⟨(w : A), hw⟩).2
    have hk₄ : conjAct (K₁ ⊔ K₂) S hc.norm s ⟨(w : A), hw⟩ = ⟨((s * w * s⁻¹ : ↥S) : A), hk₃⟩ :=
      Subtype.ext hk₂
    rw [hk₄]
    have h5' := hφ (s * w * s⁻¹) hk₃
    have hαw : ((α w : ↥S') : A') = (y : A') := by
      rw [← hwy, hφ w hw]
    have hcy : ((cS s y : ↥(K₁' ⊔ K₂')) : A') = (x : A') := by
      rw [hy, MulAut.apply_inv_self]
    rw [hcS] at hcy
    apply Subtype.ext
    rw [h5']
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hαw]
    exact hcy
  have hnorm : ∀ t : ↥S, cS t ∈ normalizer
      ((fixS (K₁' ⊔ K₂') S' : Subgroup (MulAut ↥(K₁' ⊔ K₂'))) : Set (MulAut ↥(K₁' ⊔ K₂'))) := by
    have key : ∀ (t : ↥S) (ρ : MulAut ↥(K₁' ⊔ K₂')), ρ ∈ fixS (K₁' ⊔ K₂') S' →
        cS t * ρ * (cS t)⁻¹ ∈ fixS (K₁' ⊔ K₂') S' := by
      intro t ρ hρ x hx
      rw [MulAut.mul_apply, MulAut.mul_apply, hρ ((cS t)⁻¹ x) (hinvS t x hx), MulAut.apply_inv_self]
    intro t
    rw [Subgroup.mem_normalizer_iff]
    intro ρ
    refine ⟨key t ρ, fun h => ?_⟩
    have := key t⁻¹ _ h
    rw [map_inv, inv_inv] at this
    simpa [mul_assoc] using this
  obtain ⟨o, ho, hΘo⟩ := coprime_conj_homs hc.pgroup (fixS (K₁' ⊔ K₂') S')
    (odd_card_fixS hodd h5 hmod hc') Θ cS hnorm hdiff
  have hoinv : o⁻¹ ∈ fixS (K₁' ⊔ K₂') S' := (fixS (K₁' ⊔ K₂') S').inv_mem ho
  refine ⟨φ.trans o⁻¹, ?_, ?_, ?_⟩
  · intro x hx
    have hz : ((φ ⟨(x : A), hx⟩ : ↥(K₁' ⊔ K₂')) : A') ∈ S' := by
      rw [hφ x hx]
      exact (α x).2
    show ((o⁻¹ (φ ⟨(x : A), hx⟩) : ↥(K₁' ⊔ K₂')) : A') = _
    rw [hoinv (φ ⟨(x : A), hx⟩) hz, hφ x hx]
  · intro t k hk
    have hΘφ : φ ⟨(t : A) * (k : A) * (t : A)⁻¹, hk⟩ = Θ t (φ k) := by
      have h1 : conjAct (K₁ ⊔ K₂) S hc.norm t k = ⟨(t : A) * (k : A) * (t : A)⁻¹, hk⟩ :=
        Subtype.ext (coe_conjAct (K₁ ⊔ K₂) S hc.norm t k)
      show _ = φ (conjAct (K₁ ⊔ K₂) S hc.norm t (φ.symm (φ k)))
      rw [φ.symm_apply_apply, h1]
    show ((o⁻¹ (φ ⟨(t : A) * (k : A) * (t : A)⁻¹, hk⟩) : ↥(K₁' ⊔ K₂')) : A') = _ * ((o⁻¹ (φ k) : ↥(K₁' ⊔ K₂')) : A') * _
    rw [hΘφ, hΘo t, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
    exact hcS t (o⁻¹ (φ k))
  · intro k hk
    have hu : (((φ.trans o⁻¹) k : ↥(K₁' ⊔ K₂')) : A') ∈ S' := hk
    set u := (φ.trans o⁻¹) k with hudef
    have hw : ((α.symm ⟨(u : A'), hu⟩ : ↥S) : A) ∈ K₁ ⊔ K₂ := by
      rw [hα]
      simp
    have hc1 : (((φ.trans o⁻¹) ⟨((α.symm ⟨(u : A'), hu⟩ : ↥S) : A), hw⟩ : ↥(K₁' ⊔ K₂')) : A') = (u : A') := by
      have : ((φ.trans o⁻¹) ⟨((α.symm ⟨(u : A'), hu⟩ : ↥S) : A), hw⟩ : ↥(K₁' ⊔ K₂')) =
          o⁻¹ (φ ⟨((α.symm ⟨(u : A'), hu⟩ : ↥S) : A), hw⟩) := rfl
      have hz : ((φ ⟨((α.symm ⟨(u : A'), hu⟩ : ↥S) : A), hw⟩ : ↥(K₁' ⊔ K₂')) : A') ∈ S' := by
        rw [hφ _ hw]
        exact (α _).2
      rw [this, hoinv _ hz, hφ _ hw]
      simp
    have hk' : (φ.trans o⁻¹) ⟨((α.symm ⟨(u : A'), hu⟩ : ↥S) : A), hw⟩ = (φ.trans o⁻¹) k :=
      Subtype.ext hc1
    have := (φ.trans o⁻¹).injective hk'
    rw [← this]
    exact (α.symm ⟨(u : A'), hu⟩).2

theorem rigidity_core {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A'] {F : Type} [Field F]
    [Finite F] {K₁ K₂ S : Subgroup A} {K₁' K₂' S' : Subgroup A'} (hodd : Odd (Nat.card F))
    (h5 : 5 ≤ Nat.card F) (hmod : Nat.card F % 8 = 3 ∨ Nat.card F % 8 = 5)
    (hc : FusedCfg K₁ K₂ S F) (hc' : FusedCfg K₁' K₂' S' F) (α : ↥S ≃* ↥S')
    (h₁ : ∀ x : ↥S, (x : A) ∈ K₁ ↔ ((α x : ↥S') : A') ∈ K₁')
    (h₂ : ∀ x : ↥S, (x : A) ∈ K₂ ↔ ((α x : ↥S') : A') ∈ K₂') :
    Nonempty (↥(K₁ ⊔ K₂ ⊔ S) ≃* ↥(K₁' ⊔ K₂' ⊔ S')) := by
  obtain ⟨φ, hφα, hact, hinj⟩ := exists_phi_intertwining hodd h5 hmod hc hc' α h₁ h₂
  obtain ⟨Ψ, -, -⟩ := amalgam_mulEquiv (K₁ ⊔ K₂) S (K₁' ⊔ K₂') S' hc.norm hc'.norm φ α
    (fun k t hkt => by
      have hk : k = ⟨(t : A), hkt ▸ k.2⟩ := Subtype.ext hkt
      rw [hk]
      exact hφα t _)
    (fun k hk => hinj k hk) (fun t k hk => hact t k hk)
  exact ⟨Ψ⟩

end PartC

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
