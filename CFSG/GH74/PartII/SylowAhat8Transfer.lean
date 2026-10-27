module

public import CFSG.GH74.PartII.SylowAhat8Model
public import CFSG.GH74.GLS.C3.Layer1.EvenSporTransfer

public section

namespace CFSG.GH74.PartII

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23
open CFSG.OddStandard.SmallF3.HarrisU33.Outside

@[expose] def zAhat8 : SylAhat8 := SemidirectProduct.inl ⟨0, 0, 1⟩

@[expose] def uAhat8 : SylAhat8 := SemidirectProduct.inr (Multiplicative.ofAdd 1)

private def pAhat8 : SylAhat8 := SemidirectProduct.inl ⟨1, 0, 0⟩

private def qAhat8 : SylAhat8 := SemidirectProduct.inl ⟨0, 1, 0⟩

private lemma model_facts : zAhat8 * uAhat8 = uAhat8 * zAhat8 ∧ uAhat8 * uAhat8 = 1 ∧
    zAhat8 * zAhat8 = 1 ∧ uAhat8.right ≠ 1 ∧ pAhat8 * uAhat8 = uAhat8 * pAhat8 ∧
    qAhat8 * uAhat8 = uAhat8 * qAhat8 ∧ pAhat8 * qAhat8 * pAhat8⁻¹ * qAhat8⁻¹ = zAhat8 := by
  decide +kernel

private lemma card_commute_uAhat8_sq :
    Fintype.card {g : SylAhat8 // g * uAhat8 = uAhat8 * g ∧ g * g = 1} = 12 := by
  decide +kernel

private lemma U4_pair : ∀ a b : U4, a * a = 1 → b * b = 1 → a * b = b * a →
    (a.b = 0 ∧ b.b = 0) ∨ (a.a = 0 ∧ b.a = 0) := by
  decide +kernel

private lemma half_b : (∀ v w : U4, v.b = 0 → w.b = 0 → v * w = w * v) ∧
    (∀ v : U4, v.b = 0 → v * v = 1) ∧ Fintype.card {v : U4 // v.b = 0} = 16 := by
  decide +kernel

private lemma half_a : (∀ v w : U4, v.a = 0 → w.a = 0 → v * w = w * v) ∧
    (∀ v : U4, v.a = 0 → v * v = 1) ∧ Fintype.card {v : U4 // v.a = 0} = 16 := by
  decide +kernel

private lemma eq_zAhat8_of_commute_gens : ∀ g : SylAhat8, g ≠ 1 → g * pAhat8 = pAhat8 * g →
    g * qAhat8 = qAhat8 * g →
    g * SemidirectProduct.inl ⟨omg, 0, 0⟩ = SemidirectProduct.inl ⟨omg, 0, 0⟩ * g →
    g * SemidirectProduct.inl ⟨0, omg, 0⟩ = SemidirectProduct.inl ⟨0, omg, 0⟩ * g →
    g * uAhat8 = uAhat8 * g → g = zAhat8 := by
  decide +kernel

theorem eq_zAhat8_of_commute {g : SylAhat8} (hg : g ≠ 1) (h : ∀ s : SylAhat8, g * s = s * g) :
    g = zAhat8 :=
  eq_zAhat8_of_commute_gens g hg (h _) (h _) (h _) (h _) (h _)

variable {Y : Type} [Group Y]

private lemma false_of_half {S : Subgroup Y} (e : SylAhat8 ≃* ↥S)
    (hC : centralizer {((e zAhat8 : ↥S) : Y)} ≤ S) (P : U4 → Prop) [DecidablePred P]
    (hcomm : ∀ v w : U4, P v → P w → v * w = w * v) (hsq : ∀ v : U4, P v → v * v = 1)
    (hcard : Fintype.card {v : U4 // P v} = 16) (k : Y) {a₀ b₀ : U4} (ha₀ : P a₀) (hb₀ : P b₀)
    (hx : k * (e uAhat8 : Y) * k⁻¹ = (e (SemidirectProduct.inl a₀) : Y))
    (hz : k * (e zAhat8 : Y) * k⁻¹ = (e (SemidirectProduct.inl b₀) : Y)) : False := by
  classical
  let ι : U4 → Y := fun v => ((e (SemidirectProduct.inl v) : ↥S) : Y)
  have hιmul : ∀ v w : U4, ι (v * w) = ι v * ι w := fun v w => by
    simp only [ι, map_mul, Subgroup.coe_mul]
  have hι1 : ι 1 = 1 := by simp only [ι, map_one, Subgroup.coe_one]
  have hιinj : Function.Injective ι := fun v w h =>
    SemidirectProduct.inl_injective (e.injective (Subtype.ext h))
  have hconj : ∀ v w : U4, (k⁻¹ * ι v * k) * (k⁻¹ * ι w * k) = k⁻¹ * ι (v * w) * k := by
    intro v w
    rw [hιmul]
    group
  have hx' : k * (e uAhat8 : Y) * k⁻¹ = ι a₀ := hx
  have hz' : k * (e zAhat8 : Y) * k⁻¹ = ι b₀ := hz
  have hxk : (e uAhat8 : Y) = k⁻¹ * ι a₀ * k := by
    rw [← hx']
    group
  have hzk : (e zAhat8 : Y) = k⁻¹ * ι b₀ * k := by
    rw [← hz']
    group
  have hfS : ∀ v, P v → k⁻¹ * ι v * k ∈ S := by
    intro v hv
    apply hC
    rw [mem_centralizer_singleton_iff, hzk, hconj, hconj, hcomm v b₀ hv hb₀]
  let ψ : {v : U4 // P v} → {g : SylAhat8 // g * uAhat8 = uAhat8 * g ∧ g * g = 1} :=
    fun v => ⟨e.symm ⟨k⁻¹ * ι v.1 * k, hfS v.1 v.2⟩, by
      have he : ∀ s : SylAhat8, ((e s : ↥S) : Y) = k⁻¹ * ι v.1 * k →
          s = e.symm ⟨k⁻¹ * ι v.1 * k, hfS v.1 v.2⟩ := by
        intro s hs
        rw [MulEquiv.eq_symm_apply]
        exact Subtype.ext hs
      constructor
      · apply e.injective
        apply Subtype.ext
        rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply, hxk,
          hconj, hconj, hcomm v.1 a₀ v.2 ha₀]
      · apply e.injective
        apply Subtype.ext
        rw [map_mul, Subgroup.coe_mul, MulEquiv.apply_symm_apply, hconj, hsq v.1 v.2, hι1,
          map_one, Subgroup.coe_one]
        group⟩
  have hψ : Function.Injective ψ := by
    intro v w h
    have h1 := congrArg (fun g => ((e g.1 : ↥S) : Y)) h
    simp only [ψ, MulEquiv.apply_symm_apply] at h1
    rw [mul_left_inj, mul_right_inj] at h1
    exact Subtype.ext (hιinj h1)
  have hle := Fintype.card_le_of_injective ψ hψ
  rw [hcard, card_commute_uAhat8_sq] at hle
  omega

variable [Finite Y]

theorem exists_normal_index_two_of_sylAhat8 (S : Sylow 2 Y) (e : SylAhat8 ≃* ↥S)
    (hC : centralizer {((e zAhat8 : ↥S) : Y)} ≤ (S : Subgroup Y)) :
    ∃ K : Subgroup Y, K.Normal ∧ K.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hzu, huu, hzz, hur, hpu, hqu, hpqz⟩ := model_facts
  by_contra hno
  push Not at hno
  have hcoe : ∀ a b : SylAhat8, (e (a * b) : Y) = (e a : Y) * (e b : Y) := fun a b => by
    rw [map_mul, Subgroup.coe_mul]
  let ρ : ↥S →* Multiplicative (ZMod 2) := SemidirectProduct.rightHom.comp e.symm.toMonoidHom
  let U : Subgroup Y := ρ.ker.map (S : Subgroup Y).subtype
  have hUS : U ≤ (S : Subgroup Y) := map_subtype_le _
  have hρs : Function.Surjective ρ := fun t => ⟨e (SemidirectProduct.inr t), by simp [ρ]⟩
  have hUidx : U.relIndex (S : Subgroup Y) = 2 := by
    have hsub : U.subgroupOf (S : Subgroup Y) = ρ.ker :=
      comap_map_eq_self_of_injective (subtype_injective _) _
    rw [relIndex, hsub, index_ker, MonoidHom.range_eq_top.2 hρs, card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hUmem : ∀ w ∈ U, ∃ a : U4, w = (e (SemidirectProduct.inl a) : Y) := by
    rintro w ⟨s, hs, rfl⟩
    refine ⟨(e.symm s).left, ?_⟩
    have hs' : (e.symm s).right = 1 := hs
    have h : e.symm s = SemidirectProduct.inl (e.symm s).left :=
      SemidirectProduct.ext rfl (by rw [hs', SemidirectProduct.right_inl])
    rw [← h, MulEquiv.apply_symm_apply]
    rfl
  have hmemU : ∀ s : SylAhat8, s.right = 1 → (e s : Y) ∈ U := by
    intro s hs
    refine ⟨e s, ?_, rfl⟩
    show (e.symm (e s)).right = 1
    rw [MulEquiv.symm_apply_apply]
    exact hs
  set x : Y := (e uAhat8 : Y) with hxdef
  have hxS : x ∈ (S : Subgroup Y) := (e uAhat8).2
  have hxU : x ∉ U := by
    rintro ⟨s, hs, hsx⟩
    have hs' : s = e uAhat8 := Subtype.ext hsx
    have h1 : (e.symm s).right = 1 := hs
    rw [hs', MulEquiv.symm_apply_apply] at h1
    exact hur h1
  have hxx : x * x = 1 := by
    rw [hxdef, ← hcoe, huu, map_one, Subgroup.coe_one]
  have hx1 : x ≠ 1 := fun h => hxU (h ▸ U.one_mem)
  have hmin : ∀ y ∈ (S : Subgroup Y), y ∉ U → orderOf x ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ U.one_mem)
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    have h0 := orderOf_pos y
    have hox : orderOf x = 2 := orderOf_eq_prime (by rw [sq, hxx]) hx1
    omega
  obtain ⟨g, hgU, -, hgp, hgidx⟩ := CFSG.EvenSporTransfer.exists_extremal_conj_of_thompson
    S.isPGroup' S.not_dvd_index hUS hUidx hxS hxU hmin hno
  set y : Y := g⁻¹ * x * g with hydef
  let Cy : Subgroup Y := centralizer {y}
  let P₀ : Sylow 2 ↥Cy :=
    IsPGroup.toSylow (P := ((S : Subgroup Y) ⊓ Cy).subgroupOf Cy) hgp.comap_subtype hgidx
  let φ : ↥Cy →* Y := (MulAut.conj g).toMonoidHom.comp Cy.subtype
  have hφ : Function.Injective φ := fun a b h => by
    simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, mul_left_inj, mul_right_inj] at h
    exact Subtype.ext h
  have hQp : IsPGroup 2 ↥(((S : Subgroup Y) ⊓ centralizer {x}).comap φ) :=
    S.isPGroup'.to_inf_left.comap_of_injective φ hφ
  obtain ⟨P₁, hQP₁⟩ := hQp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (↥Cy) P₁ P₀
  set k : Y := (c : Y) * g⁻¹ with hkdef
  have hcy : (c : Y) * y = y * (c : Y) := mem_centralizer_singleton_iff.1 c.2
  have hk : ∀ d ∈ (S : Subgroup Y), d * x = x * d → k * d * k⁻¹ ∈ (S : Subgroup Y) := by
    intro d hdS hdx
    have hdC : g⁻¹ * d * g ∈ Cy := by
      rw [mem_centralizer_singleton_iff, hydef]
      calc g⁻¹ * d * g * (g⁻¹ * x * g) = g⁻¹ * (d * x) * g := by group
        _ = g⁻¹ * (x * d) * g := by rw [hdx]
        _ = g⁻¹ * x * g * (g⁻¹ * d * g) := by group
    have hdQ : (⟨g⁻¹ * d * g, hdC⟩ : ↥Cy) ∈ ((S : Subgroup Y) ⊓ centralizer {x}).comap φ := by
      rw [mem_comap]
      have hφd : φ ⟨g⁻¹ * d * g, hdC⟩ = d := by
        simp only [φ, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
          MulAut.conj_apply, Subgroup.coe_subtype]
        group
      rw [hφd]
      exact mem_inf.2 ⟨hdS, mem_centralizer_singleton_iff.2 hdx⟩
    have hP₀ : (P₀ : Subgroup ↥Cy) = ((S : Subgroup Y) ⊓ Cy).subgroupOf Cy :=
      IsPGroup.toSylow_coe _ _
    have h1 := Subgroup.smul_mem_pointwise_smul _ (MulAut.conj c) _ (hQP₁ hdQ)
    rw [← Sylow.coe_subgroup_smul, hc, hP₀, mem_subgroupOf] at h1
    have h2 := (mem_inf.1 h1).1
    simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    have e1 : k * d * k⁻¹ = (c : Y) * (g⁻¹ * d * g) * (c : Y)⁻¹ := by
      rw [hkdef]
      group
    rw [e1]
    exact h2
  have hy : k * x * k⁻¹ = y := by
    calc k * x * k⁻¹ = (c : Y) * y * (c : Y)⁻¹ := by rw [hkdef, hydef]; group
      _ = y := by rw [hcy]; group
  obtain ⟨a₀, ha₀⟩ := hUmem y hgU
  have hp := hk (e pAhat8 : Y) (e pAhat8).2 (by rw [hxdef, ← hcoe, ← hcoe, hpu])
  have hq := hk (e qAhat8 : Y) (e qAhat8).2 (by rw [hxdef, ← hcoe, ← hcoe, hqu])
  obtain ⟨s₁, hs₁⟩ : ∃ s₁ : SylAhat8, (e s₁ : Y) = k * (e pAhat8 : Y) * k⁻¹ :=
    ⟨e.symm ⟨_, hp⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  obtain ⟨s₂, hs₂⟩ : ∃ s₂ : SylAhat8, (e s₂ : Y) = k * (e qAhat8 : Y) * k⁻¹ :=
    ⟨e.symm ⟨_, hq⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  have hz' : k * (e zAhat8 : Y) * k⁻¹ = (e (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) : Y) := by
    have h1 : (e (s₁ * s₂ * s₁⁻¹ * s₂⁻¹) : Y) =
        (e s₁ : Y) * (e s₂ : Y) * (e s₁ : Y)⁻¹ * (e s₂ : Y)⁻¹ := by
      simp only [map_mul, map_inv]
      rfl
    have h2 : (e zAhat8 : Y) =
        (e pAhat8 : Y) * (e qAhat8 : Y) * (e pAhat8 : Y)⁻¹ * (e qAhat8 : Y)⁻¹ := by
      rw [← hpqz]
      simp only [map_mul, map_inv]
      rfl
    rw [h1, hs₁, hs₂, h2]
    group
  have hzU : k * (e zAhat8 : Y) * k⁻¹ ∈ U := by
    rw [hz']
    apply hmemU
    simp only [SemidirectProduct.mul_right, SemidirectProduct.inv_right]
    rw [mul_right_comm s₁.right s₂.right, mul_inv_cancel, one_mul, mul_inv_cancel]
  obtain ⟨b₀, hb₀⟩ := hUmem _ hzU
  have hι : Function.Injective fun v : U4 => (e (SemidirectProduct.inl v) : Y) :=
    fun v w h => SemidirectProduct.inl_injective (e.injective (Subtype.ext h))
  have hιmul : ∀ v w : U4, (e (SemidirectProduct.inl (v * w)) : Y) =
      (e (SemidirectProduct.inl v) : Y) * (e (SemidirectProduct.inl w) : Y) := fun v w => by
    rw [map_mul, hcoe]
  have hι1 : (e (SemidirectProduct.inl (1 : U4)) : Y) = 1 := by
    rw [map_one, map_one, Subgroup.coe_one]
  have hyy : y * y = 1 := by
    rw [hydef]
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = 1 := by rw [hxx]; group
  have hzz' : (k * (e zAhat8 : Y) * k⁻¹) * (k * (e zAhat8 : Y) * k⁻¹) = 1 := by
    calc (k * (e zAhat8 : Y) * k⁻¹) * (k * (e zAhat8 : Y) * k⁻¹) =
        k * ((e zAhat8 : Y) * (e zAhat8 : Y)) * k⁻¹ := by group
      _ = 1 := by rw [← hcoe, hzz, map_one, Subgroup.coe_one]; group
  have hyz : y * (k * (e zAhat8 : Y) * k⁻¹) = (k * (e zAhat8 : Y) * k⁻¹) * y := by
    rw [← hy]
    calc k * x * k⁻¹ * (k * (e zAhat8 : Y) * k⁻¹) = k * (x * (e zAhat8 : Y)) * k⁻¹ := by group
      _ = k * ((e zAhat8 : Y) * x) * k⁻¹ := by rw [hxdef, ← hcoe, ← hcoe, hzu]
      _ = k * (e zAhat8 : Y) * k⁻¹ * (k * x * k⁻¹) := by group
  have ha₀a₀ : a₀ * a₀ = 1 := hι (by
    show (e (SemidirectProduct.inl (a₀ * a₀)) : Y) = (e (SemidirectProduct.inl 1) : Y)
    rw [hιmul, ← ha₀, hyy, hι1])
  have hb₀b₀ : b₀ * b₀ = 1 := hι (by
    show (e (SemidirectProduct.inl (b₀ * b₀)) : Y) = (e (SemidirectProduct.inl 1) : Y)
    rw [hιmul, ← hb₀, hzz', hι1])
  have ha₀b₀ : a₀ * b₀ = b₀ * a₀ := hι (by
    show (e (SemidirectProduct.inl (a₀ * b₀)) : Y) = (e (SemidirectProduct.inl (b₀ * a₀)) : Y)
    rw [hιmul, hιmul, ← ha₀, ← hb₀, hyz])
  rcases U4_pair a₀ b₀ ha₀a₀ hb₀b₀ ha₀b₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨hcomm, hsq, hcard⟩ := half_b
    exact false_of_half e hC (fun v => v.b = 0) hcomm hsq hcard k h1 h2 (hy.trans ha₀) hb₀
  · obtain ⟨hcomm, hsq, hcard⟩ := half_a
    exact false_of_half e hC (fun v => v.a = 0) hcomm hsq hcard k h1 h2 (hy.trans ha₀) hb₀

theorem exists_normal_index_two_of_centralizer_eq_sylAhat8 (S : Sylow 2 Y) (e : SylAhat8 ≃* ↥S)
    {d : Y} (hd : d ≠ 1) (hCent : centralizer {d} = (S : Subgroup Y)) :
    ∃ K : Subgroup Y, K.Normal ∧ K.index = 2 := by
  have hdS : d ∈ (S : Subgroup Y) := hCent ▸ mem_centralizer_singleton_iff.2 rfl
  have hz : e zAhat8 = ⟨d, hdS⟩ := by
    have h := eq_zAhat8_of_commute (g := e.symm ⟨d, hdS⟩) ?_ ?_
    · rw [← h, MulEquiv.apply_symm_apply]
    · intro h1
      apply hd
      have h2 := congrArg (fun s => ((e s : ↥S) : Y)) h1
      simpa using h2
    · intro s
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      apply Subtype.ext
      show d * (e s : Y) = (e s : Y) * d
      have hs : (e s : Y) ∈ centralizer {d} := hCent ▸ (e s).2
      exact (mem_centralizer_singleton_iff.1 hs).symm
  refine exists_normal_index_two_of_sylAhat8 S e ?_
  rw [hz]
  exact hCent.le

end CFSG.GH74.PartII
