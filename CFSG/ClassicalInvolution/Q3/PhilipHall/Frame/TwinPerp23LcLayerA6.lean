module

public import CFSG.LocalAnalysis.ComponentClassification.Layer

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc

open CFSG CFSG.Open
open scoped commutatorElement

private theorem la6_perfect {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 6)) :
    Group.IsPerfect K := by
  haveI : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem la6_isQuasisimple {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 6)) :
    CFSG.Open.IsQuasisimple K := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup K := e.isSimpleGroup
  haveI : Group.IsPerfect K := la6_perfect e
  have hcen : Subgroup.center K = ⊥ := by
    refine (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center K)).resolve_right fun h => ?_
    have : IsMulCommutative K := Subgroup.center_eq_top_iff.mp h
    exact Group.IsPerfect.not_isMulCommutative K this
  refine ⟨Group.IsPerfect.commutator_eq_top (G := K), ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).isSimpleGroup

private def la6_conjAut {G : Type*} [Group G] (S : Subgroup G) (g : G)
    (h : ∀ x ∈ S, g * x * g⁻¹ ∈ S) (h' : ∀ x ∈ S, g⁻¹ * x * g ∈ S) : MulAut ↥S where
  toFun x := ⟨g * x * g⁻¹, h x x.2⟩
  invFun x := ⟨g⁻¹ * x * g, h' x x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

private theorem la6_inv_conj {G : Type*} [Group G] {a : G} (ha3 : a ^ 3 = 1) {S : Subgroup G}
    (h : ∀ x ∈ S, a * x * a⁻¹ ∈ S) : ∀ x ∈ S, a⁻¹ * x * a ∈ S := by
  intro x hx
  have h3 : a * a * a = 1 := by
    have h := ha3
    rwa [pow_succ, pow_two] at h
  have hinv : a⁻¹ = a * a := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact h3)
  have hinv2 : a⁻¹ * a⁻¹ = a := by rw [← mul_inv_rev, ← hinv, inv_inv]
  have : a⁻¹ * x * a = a * (a * x * a⁻¹) * a⁻¹ := by
    calc a⁻¹ * x * a = (a * a) * x * (a⁻¹ * a⁻¹) := by rw [← hinv, hinv2]
      _ = a * (a * x * a⁻¹) * a⁻¹ := by group
  rw [this]
  exact h _ (h x hx)

private theorem la6_comm_mul {G : Type*} [Group G] {r r' d d' : G}
    (h1 : Commute r d) (h2 : Commute r d') (h3 : Commute r' d) (h4 : Commute r' d')
    (h5 : Commute d d') :
    r * d * (r' * d') * (r * d)⁻¹ * (r' * d')⁻¹ = r * r' * r⁻¹ * r'⁻¹ := by
  have e1 : r * d * (r' * d') = r * r' * (d * d') := h3.symm.mul_mul_mul_comm r d'
  have e3 : d * d' * d⁻¹ = d' := h5.mul_inv_cancel
  have e4 : d' * r⁻¹ = r⁻¹ * d' := h2.inv_left.eq.symm
  calc r * d * (r' * d') * (r * d)⁻¹ * (r' * d')⁻¹
      = r * r' * ((d * d' * d⁻¹) * r⁻¹ * d'⁻¹ * r'⁻¹) := by rw [e1]; group
    _ = r * r' * (d' * r⁻¹ * d'⁻¹ * r'⁻¹) := by rw [e3]
    _ = r * r' * (r⁻¹ * d' * d'⁻¹ * r'⁻¹) := by rw [e4]
    _ = r * r' * r⁻¹ * r'⁻¹ := by group

private theorem la6_decomp {G : Type} [Group G] {F L A : Subgroup G} {a : G}
    (haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (ha3 : a ^ 3 = 1)
    (hAF : A ≤ F) (hAnorm : ∀ f ∈ F, ∀ x ∈ A, f * x * f⁻¹ ∈ A)
    (e : ↥A ≃* alternatingGroup (Fin 6))
    (hAD : ∀ x ∈ ComponentClassification.Layer.subgroup ↥F,
      ∃ r ∈ A, ∃ d ∈ F, (∀ l ∈ L, d * l = l * d) ∧ (x : G) = r * d) :
    ∀ x ∈ A, ∃ r ∈ A, ∃ d ∈ F, (∀ l ∈ L, d * l = l * d) ∧ a * x * a⁻¹ = r * d := by
  have hnormal : (A.subgroupOf F).Normal := ⟨fun n hn g => hAnorm g g.2 n hn⟩
  have hq : CFSG.Open.IsQuasisimple ↥(A.subgroupOf F) :=
    la6_isQuasisimple ((Subgroup.subgroupOfEquivOfLe hAF).trans e)
  have hcomp : CFSG.Open.IsComponentOf (A.subgroupOf F) ⊤ :=
    ⟨le_top, CFSG.Open.IsSubnormal.step le_top (hnormal.subgroupOf ⊤)
      (CFSG.Open.IsSubnormal.refl ⊤), hq⟩
  have hle := ComponentClassification.Layer.component_le hcomp
  let η : MulAut ↥F := la6_conjAut F a haF (la6_inv_conj ha3 haF)
  intro x hx
  have hxF : x ∈ F := hAF hx
  have hmem : (⟨x, hxF⟩ : ↥F) ∈ ComponentClassification.Layer.subgroup ↥F :=
    hle (show (⟨x, hxF⟩ : ↥F) ∈ A.subgroupOf F from hx)
  have hmem' : η ⟨x, hxF⟩ ∈ ComponentClassification.Layer.subgroup ↥F :=
    ComponentClassification.Layer.map_le_of_equiv η (Subgroup.mem_map_of_mem η.toMonoidHom hmem)
  obtain ⟨r, hr, d, hd, hdc, hη⟩ := hAD _ hmem'
  exact ⟨r, hr, d, hd, hdc, hη⟩

private theorem la6_normalizes {G : Type*} [Group G] {L A : Subgroup G} {a : G}
    (hperf : Group.IsPerfect ↥A) (hAL : A ≤ L) (D : G → Prop)
    (hDa : ∀ h, D h → a * h = h * a) (hDL : ∀ h, D h → ∀ l ∈ L, h * l = l * h)
    (hdec : ∀ x ∈ A, ∃ r ∈ A, ∃ d, D d ∧ a * x * a⁻¹ = r * d) :
    ∀ x ∈ A, a * x * a⁻¹ ∈ A := by
  have key : ∀ x ∈ A, ∃ r ∈ A, ∃ d, D d ∧ a * x * a⁻¹ = r * d ∧ ∀ h, D h → Commute d h := by
    intro x hx
    obtain ⟨r, hr, d, hd, hxe⟩ := hdec x hx
    refine ⟨r, hr, d, hd, hxe, fun h hh => ?_⟩
    have hdr : d = r⁻¹ * (a * x * a⁻¹) := by rw [hxe]; group
    have h1 : Commute r h := (hDL h hh r (hAL hr)).symm
    have h2 : Commute x h := (hDL h hh x (hAL hx)).symm
    have h3 : Commute a h := hDa h hh
    rw [hdr]
    exact h1.inv_left.mul_left ((h3.mul_left h2).mul_left h3.inv_left)
  let K : Subgroup G := A ⊓ A.comap (MulAut.conj a).toMonoidHom
  have hcomm : ⁅A, A⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨r, hr, d, hd, hxe, hdc⟩ := key x hx
    obtain ⟨r', hr', d', hd', hye, -⟩ := key y hy
    have hxy : a * ⁅x, y⁆ * a⁻¹ = ⁅r, r'⁆ := by
      calc a * ⁅x, y⁆ * a⁻¹
          = (a * x * a⁻¹) * (a * y * a⁻¹) * (a * x * a⁻¹)⁻¹ * (a * y * a⁻¹)⁻¹ := by
            simp only [commutatorElement_def]; group
        _ = r * d * (r' * d') * (r * d)⁻¹ * (r' * d')⁻¹ := by rw [hxe, hye]
        _ = r * r' * r⁻¹ * r'⁻¹ :=
            la6_comm_mul (hDL d hd r (hAL hr)).symm (hDL d' hd' r (hAL hr)).symm
              (hDL d hd r' (hAL hr')).symm (hDL d' hd' r' (hAL hr')).symm (hdc d' hd')
        _ = ⁅r, r'⁆ := by simp only [commutatorElement_def]
    have hAr : ⁅r, r'⁆ ∈ A := by
      simp only [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hr hr') (A.inv_mem hr)) (A.inv_mem hr')
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_comap.mpr ?_⟩
    · simp only [commutatorElement_def]
      exact A.mul_mem (A.mul_mem (A.mul_mem hx hy) (A.inv_mem hx)) (A.inv_mem hy)
    · show a * ⁅x, y⁆ * a⁻¹ ∈ A
      rw [hxy]
      exact hAr
  haveI := hperf
  have hAK : A ≤ K := by
    calc A = ⁅A, A⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ K := hcomm
  intro x hx
  exact Subgroup.mem_comap.mp (Subgroup.mem_inf.mp (hAK hx)).2

private theorem la6_central_of_alt {G : Type} [Group G] [Finite G] {F L A : Subgroup G} {a w : G}
    (haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (ha3 : a ^ 3 = 1) (hwF : w ∈ F) (hw2 : w * w = 1)
    (haw : a * w = w * a) (hfix : ∀ x ∈ F, x * w = w * x → a * x = x * a)
    (hDw : ∀ x ∈ F, (∀ l ∈ L, x * l = l * x) → x * w = w * x)
    (hAL : A ≤ L) (hAF : A ≤ F) (hAnorm : ∀ f ∈ F, ∀ x ∈ A, f * x * f⁻¹ ∈ A)
    (e : ↥A ≃* alternatingGroup (Fin 6))
    (hAD : ∀ x ∈ ComponentClassification.Layer.subgroup ↥F,
      ∃ r ∈ A, ∃ d ∈ F, (∀ l ∈ L, d * l = l * d) ∧ (x : G) = r * d)
    (hA6 : ∀ (B : Type) [Group B] [Finite B], Nonempty (B ≃* alternatingGroup (Fin 6)) →
      ∀ f α : MulAut B, f * f = 1 → f ≠ 1 → α * α * α = 1 → α * f = f * α →
        (∀ x, f x = x → α x = x) → α = 1) :
    ∀ x ∈ A, a * x = x * a := by
  have hdec := la6_decomp haF ha3 hAF hAnorm e hAD
  have hnorm : ∀ x ∈ A, a * x * a⁻¹ ∈ A :=
    la6_normalizes (la6_perfect e) hAL (fun d => d ∈ F ∧ ∀ l ∈ L, d * l = l * d)
      (fun d hd => hfix d hd.1 (hDw d hd.1 hd.2)) (fun d hd => hd.2)
      (fun x hx => by
        obtain ⟨r, hr, d, hd, hdc, h⟩ := hdec x hx
        exact ⟨r, hr, d, ⟨hd, hdc⟩, h⟩)
  have hnorm' : ∀ x ∈ A, a⁻¹ * x * a ∈ A := la6_inv_conj ha3 hnorm
  have hwA' : ∀ x ∈ A, w⁻¹ * x * w ∈ A := fun x hx => by
    simpa using hAnorm w⁻¹ (F.inv_mem hwF) x hx
  let α : MulAut ↥A := la6_conjAut A a hnorm hnorm'
  let f : MulAut ↥A := la6_conjAut A w (hAnorm w hwF) hwA'
  have h3 : a * a * a = 1 := by
    have h := ha3
    rwa [pow_succ, pow_two] at h
  have hα3 : α * α * α = 1 := by
    ext x
    show a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹ = x
    calc a * (a * (a * (x : G) * a⁻¹) * a⁻¹) * a⁻¹
        = (a * a * a) * (x : G) * (a * a * a)⁻¹ := by group
      _ = x := by rw [h3]; group
  have hf2 : f * f = 1 := by
    ext x
    show w * (w * (x : G) * w⁻¹) * w⁻¹ = x
    calc w * (w * (x : G) * w⁻¹) * w⁻¹ = (w * w) * (x : G) * (w * w)⁻¹ := by group
      _ = x := by rw [hw2]; group
  have hαf : α * f = f * α := by
    ext x
    show a * (w * (x : G) * w⁻¹) * a⁻¹ = w * (a * (x : G) * a⁻¹) * w⁻¹
    calc a * (w * (x : G) * w⁻¹) * a⁻¹ = (a * w) * (x : G) * (a * w)⁻¹ := by group
      _ = (w * a) * (x : G) * (w * a)⁻¹ := by rw [haw]
      _ = w * (a * (x : G) * a⁻¹) * w⁻¹ := by group
  have hfix' : ∀ x, f x = x → α x = x := by
    intro x hx
    have hx' : w * (x : G) * w⁻¹ = x := congrArg Subtype.val hx
    have hxw : (x : G) * w = w * (x : G) := by
      calc (x : G) * w = (w * (x : G) * w⁻¹) * w := by rw [hx']
        _ = w * (x : G) := by group
    have hax : a * (x : G) = (x : G) * a := hfix x (hAF x.2) hxw
    apply Subtype.ext
    show a * (x : G) * a⁻¹ = x
    rw [hax]; group
  have hα1 : ∀ x : ↥A, α x = x := by
    by_cases hf1 : f = 1
    · intro x
      exact hfix' x (by rw [hf1]; rfl)
    · intro x
      rw [hA6 ↥A ⟨e⟩ f α hf2 hf1 hα3 hαf hfix']
      rfl
  intro x hx
  have h := congrArg Subtype.val (hα1 ⟨x, hx⟩)
  have h' : a * x * a⁻¹ = x := h
  calc a * x = a * x * a⁻¹ * a := by group
    _ = x * a := by rw [h']

theorem layer_central_of_mul {G : Type} [Group G] [Finite G] {F L A : Subgroup G} {a w : G}
    (haF : ∀ x ∈ F, a * x * a⁻¹ ∈ F) (ha3 : a ^ 3 = 1) (hwF : w ∈ F) (hw2 : w * w = 1)
    (haw : a * w = w * a) (hfix : ∀ x ∈ F, x * w = w * x → a * x = x * a)
    (hDw : ∀ x ∈ F, (∀ l ∈ L, x * l = l * x) → x * w = w * x)
    (hAL : A ≤ L) (hAF : A ≤ F) (hAnorm : ∀ f ∈ F, ∀ x ∈ A, f * x * f⁻¹ ∈ A)
    (hAtype : A = ⊥ ∨ Nonempty (↥A ≃* alternatingGroup (Fin 6)))
    (hAD : ∀ x ∈ ComponentClassification.Layer.subgroup ↥F,
      ∃ r ∈ A, ∃ d ∈ F, (∀ l ∈ L, d * l = l * d) ∧ (x : G) = r * d)
    (hA6 : ∀ (B : Type) [Group B] [Finite B], Nonempty (B ≃* alternatingGroup (Fin 6)) →
      ∀ f α : MulAut B, f * f = 1 → f ≠ 1 → α * α * α = 1 → α * f = f * α →
        (∀ x, f x = x → α x = x) → α = 1) :
    ∀ x ∈ ComponentClassification.Layer.subgroup ↥F, a * (x : G) = (x : G) * a := by
  have hacent : ∀ x ∈ A, a * x = x * a := by
    rcases hAtype with hbot | ⟨⟨e⟩⟩
    · intro x hx
      rw [hbot, Subgroup.mem_bot] at hx
      rw [hx, mul_one, one_mul]
    · exact la6_central_of_alt haF ha3 hwF hw2 haw hfix hDw hAL hAF hAnorm e hAD hA6
  intro x hx
  obtain ⟨r, hr, d, hd, hdc, hxrd⟩ := hAD x hx
  rw [hxrd]
  calc a * (r * d) = (a * r) * d := (mul_assoc _ _ _).symm
    _ = (r * a) * d := by rw [hacent r hr]
    _ = r * (a * d) := mul_assoc _ _ _
    _ = r * (d * a) := by rw [hfix d hd (hDw d hd hdc)]
    _ = r * d * a := (mul_assoc _ _ _).symm

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Lc
