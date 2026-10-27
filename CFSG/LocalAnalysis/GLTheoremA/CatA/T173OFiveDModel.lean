module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotNeighbourParam

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173

variable {Ω : Type} [Group Ω] {S B : Subgroup Ω} {Γ : Type} [Group Γ] {G₀ Ghat : Subgroup Γ}

theorem le_normalizer_of_splitInnerDiagMarking16 {p : ℕ}
    (h : SplitInnerDiagMarking16 p B S) : B ≤ Subgroup.normalizer (S : Set Ω) := by
  obtain ⟨-, lab, -, hraw⟩ := h
  obtain ⟨R, hR, I, F, θ, hs, hna, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact hP.2.1

namespace S172DModel

variable (M : S172DModel S B G₀ Ghat)

private lemma mem_centralizer_of_β_eq_one [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) {b : ↥B}
    (hb : M.β b = 1) : (b : Ω) ∈ Subgroup.centralizer (S : Set Ω) := by
  have hN : B ≤ Subgroup.normalizer (S : Set Ω) :=
    le_normalizer_of_splitInnerDiagMarking16 hcfg.split
  haveI : Group.IsPerfect ↥S := ⟨hcfg.split.1⟩
  have hmem : ∀ t : ↥S, (b : Ω)⁻¹ * (t : Ω) * (b : Ω) ∈ S := by
    intro t
    simpa using
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hN b.2)) (t : Ω)).mp t.2
  let φ : ↥S →* ↥S :=
    { toFun := fun t => ⟨(b : Ω)⁻¹ * (t : Ω) * (b : Ω), hmem t⟩
      map_one' := by ext; simp
      map_mul' := fun s t => by ext; simp only [Subgroup.coe_mul]; group }
  have hφ : ∀ t : ↥S, M.π (φ t) = M.π t := by
    intro t
    have hc := M.conj b t (φ t) rfl
    simpa [φ, hb] using hc
  have hφid : φ = MonoidHom.id ↥S :=
    CFSG.SeitzReduction.LinearPilot.eq_of_comp_eq_of_ker_le_center (p := M.π)
      (by rw [M.ker_π]) (φ := φ) (ψ := MonoidHom.id ↥S) hφ
  have hfix : ∀ t : ↥S, (b : Ω)⁻¹ * (t : Ω) * (b : Ω) = (t : Ω) := by
    intro t
    have h := congrArg (fun f : ↥S →* ↥S => ((f t : ↥S) : Ω)) hφid
    simpa [φ] using h
  refine Subgroup.mem_centralizer_iff.2 ?_
  intro t ht
  have h := hfix ⟨t, ht⟩
  calc t * b = b * ((b : Ω)⁻¹ * t * b) := by group
    _ = b * t := by rw [h]

private lemma β_eq_one_of_mem_centralizer (M : S172DModel S B G₀ Ghat) {b : ↥B}
    (hb : (b : Ω) ∈ Subgroup.centralizer (S : Set Ω)) : M.β b = 1 := by
  apply Subtype.ext
  apply M.faithful (M.β b) (M.β b).2
  intro h hh
  obtain ⟨t, ht⟩ := M.surj ⟨h, hh⟩
  have hct : (t : Ω) * b = b * t :=
    Subgroup.mem_centralizer_iff.1 hb (t : Ω) t.2
  have hfix : (b : Ω)⁻¹ * (t : Ω) * (b : Ω) = (t : Ω) := by
    calc (b : Ω)⁻¹ * (t : Ω) * (b : Ω) = (b : Ω)⁻¹ * ((t : Ω) * (b : Ω)) := by group
      _ = (b : Ω)⁻¹ * ((b : Ω) * (t : Ω)) := by rw [hct]
      _ = (t : Ω) := by group
  have hc := M.conj b t t hfix.symm
  have eqt : ((M.π t : ↥G₀) : Γ) = h := congrArg Subtype.val ht
  have h3 : ((M.β b : ↥Ghat) : Γ) * ((M.π t : ↥G₀) : Γ) =
      ((M.π t : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by
    calc ((M.β b : ↥Ghat) : Γ) * ((M.π t : ↥G₀) : Γ) =
        ((M.β b : ↥Ghat) : Γ) *
          (((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ)) := by
          conv_lhs => rw [hc]
      _ = ((M.π t : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) := by group
  rw [eqt] at h3
  exact h3

theorem ker_β [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω} (hcfg : Cfg173 p S B N D K x)
    (M : S172DModel S B G₀ Ghat) : M.β.ker = (Subgroup.zpowers x).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun hb => (hcfg.cent b b.2).mp (mem_centralizer_of_β_eq_one hcfg M hb),
    fun hb => β_eq_one_of_mem_centralizer M ((hcfg.cent b b.2).mpr hb)⟩

private lemma conjAction_eq_of_coe_eq (M : S172DModel S B G₀ Ghat) {b : ↥B} {s : ↥S}
    (hbs : (b : Ω) = (s : Ω)) :
    ∀ h' ∈ G₀, (((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹) * h' =
      h' * (((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹) := by
  have hmem : ∀ t : ↥S, (b : Ω)⁻¹ * (t : Ω) * (b : Ω) ∈ S := by
    intro t
    rw [hbs]
    exact S.mul_mem (S.mul_mem (S.inv_mem s.2) t.2) s.2
  have hconj : ∀ t : ↥S,
      ((M.π ⟨(b : Ω)⁻¹ * (t : Ω) * (b : Ω), hmem t⟩ : ↥G₀) : Γ) =
        ((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) :=
    fun t => M.conj b t ⟨_, hmem t⟩ rfl
  have hπ : ∀ t : ↥S,
      ((M.π ⟨(b : Ω)⁻¹ * (t : Ω) * (b : Ω), hmem t⟩ : ↥G₀) : Γ) =
        ((M.π s : ↥G₀) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.π s : ↥G₀) : Γ) := by
    intro t
    have e : (⟨(b : Ω)⁻¹ * (t : Ω) * (b : Ω), hmem t⟩ : ↥S) = s⁻¹ * t * s := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hbs]
    rw [e, map_mul, map_mul, map_inv]
    rfl
  intro h' hh'
  obtain ⟨t, ht⟩ := M.surj ⟨h', hh'⟩
  have h2 : ((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ) =
      ((M.π s : ↥G₀) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.π s : ↥G₀) : Γ) :=
    (hconj t).symm.trans (hπ t)
  have h3 : (((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹) * ((M.π t : ↥G₀) : Γ) =
      ((M.π t : ↥G₀) : Γ) * (((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹) := by
    calc (((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹) * ((M.π t : ↥G₀) : Γ) =
        ((M.β b : ↥Ghat) : Γ) * (((M.π s : ↥G₀) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ)) := by group
      _ = ((M.β b : ↥Ghat) : Γ) *
          (((M.π s : ↥G₀) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.π s : ↥G₀) : Γ)) *
            ((M.π s : ↥G₀) : Γ)⁻¹ := by group
      _ = ((M.β b : ↥Ghat) : Γ) *
          (((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π t : ↥G₀) : Γ) * ((M.β b : ↥Ghat) : Γ)) *
            ((M.π s : ↥G₀) : Γ)⁻¹ := by rw [← h2]
      _ = ((M.π t : ↥G₀) : Γ) * (((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹) := by group
  have eqt : ((M.π t : ↥G₀) : Γ) = h' := congrArg Subtype.val ht
  rw [eqt] at h3
  exact h3

theorem coe_β_eq_coe_π (M : S172DModel S B G₀ Ghat) {b : ↥B} {s : ↥S}
    (h : (b : Ω) = s) : ((M.β b : ↥Ghat) : Γ) = ((M.π s : ↥G₀) : Γ) := by
  have hbs : (b : Ω) = (s : Ω) := h
  have hcGhat : ((M.β b : ↥Ghat) : Γ) * ((M.π s : ↥G₀) : Γ)⁻¹ ∈ Ghat :=
    Ghat.mul_mem (M.β b).2 (Ghat.inv_mem (M.le (M.π s).2))
  have h1 := M.faithful _ hcGhat (conjAction_eq_of_coe_eq M hbs)
  exact mul_inv_eq_one.mp h1

theorem card_eq_mul_card_barB [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) :
    Nat.card B = p * Nat.card M.barB := by
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  have hx : orderOf x = p := orderOf_eq_prime (hcfg.elem.2 x hcfg.mem) hcfg.ne_one
  have hker : Nat.card M.β.ker = p := by
    rw [ker_β hcfg M,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.2 hcfg.mem)).toEquiv,
      Nat.card_zpowers, hx]
  have hrange : Nat.card M.β.range = Nat.card M.barB :=
    (Subgroup.card_map_of_injective Ghat.subtype_injective).symm
  have h := Subgroup.card_ker_mul_card_range M.β
  rw [hker, hrange] at h
  exact h.symm

theorem isElemAbelian_barB [Finite Ω] {p : ℕ} {N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (M : S172DModel S B G₀ Ghat) : IsElemAbelian p M.barB := by
  have h1 : IsElemAbelian p ((B.subgroupOf B).map M.β) := (hcfg.elem.subgroupOf B).map M.β
  rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h1
  exact h1.map Ghat.subtype

private def conjEnd (g : Γ) : Γ →* Γ := (MulAut.conj g).toMonoidHom

private lemma conjEnd_apply (g x : Γ) : conjEnd g x = g * x * g⁻¹ := rfl

private def conjOn {H : Subgroup Γ} (g : Γ) (hmem : ∀ x ∈ H, conjEnd g x ∈ H) :
    ↥H →* ↥H where
  toFun x := ⟨conjEnd g x, hmem x x.2⟩
  map_one' := by ext; simp [conjEnd]
  map_mul' a b := by ext; simp only [Subgroup.coe_mul, map_mul]

private lemma conjOn_coe {H : Subgroup Γ} {g : Γ} {hmem : ∀ x ∈ H, conjEnd g x ∈ H}
    (x : ↥H) : ((conjOn g hmem x : ↥H) : Γ) = conjEnd g x := rfl

private lemma conjOn_injective {H : Subgroup Γ} {g : Γ} {hmem : ∀ x ∈ H, conjEnd g x ∈ H} :
    Function.Injective (conjOn g hmem) := by
  intro a b hab
  have h : conjEnd g ((a : ↥H) : Γ) = conjEnd g ((b : ↥H) : Γ) := by
    simpa [conjOn_coe] using congrArg Subtype.val hab
  exact Subtype.ext ((MulAut.conj g).injective (by simpa [conjEnd] using h))

private lemma conjEnd_mem_G₀ {g : Γ} (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ))
    {x : Γ} (hx : x ∈ G₀) : conjEnd g x ∈ G₀ := by
  simpa [conjEnd, MulAut.conj_apply] using (Subgroup.mem_normalizer_iff.mp hgN x).mp hx

private lemma conjEnd_inv_mem_G₀ {g : Γ} (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ))
    {x : Γ} (hx : x ∈ G₀) : g⁻¹ * x * g ∈ G₀ := by
  simpa [MulAut.conj_apply] using
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) x).mp hx

private lemma conjEnd_mem_Ghat {g : Γ} (hg : g ∈ Ghat) {x : Γ} (hx : x ∈ Ghat) :
    conjEnd g x ∈ Ghat := by
  simpa [conjEnd, MulAut.conj_apply] using
    Ghat.mul_mem (Ghat.mul_mem hg hx) (Ghat.inv_mem hg)

private def conjG₀ (g : Γ) (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) :
    ↥G₀ →* ↥G₀ := conjOn g fun x hx => conjEnd_mem_G₀ hgN hx

private def conjGhat (g : Γ) (hg : g ∈ Ghat) : ↥Ghat →* ↥Ghat :=
  conjOn g fun x hx => conjEnd_mem_Ghat hg hx

private lemma conjG₀_surj (M : S172DModel S B G₀ Ghat) {g : Γ}
    (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) :
    Function.Surjective ((conjG₀ g hgN).comp M.π) := by
  intro y
  obtain ⟨s, hs⟩ := M.surj ⟨g⁻¹ * (y : Γ) * g, conjEnd_inv_mem_G₀ hgN y.2⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  have hy : ((M.π s : ↥G₀) : Γ) = g⁻¹ * (y : Γ) * g := by rw [hs]
  show conjEnd g ((M.π s : ↥G₀) : Γ) = (y : Γ)
  rw [hy, conjEnd_apply]
  group

private lemma conjG₀_ker (M : S172DModel S B G₀ Ghat) {g : Γ}
    (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) :
    ((conjG₀ g hgN).comp M.π).ker = Subgroup.center ↥S :=
  (MonoidHom.ker_comp_of_injective M.π _
    (conjOn_injective (H := G₀) (hmem := fun x hx => conjEnd_mem_G₀ hgN hx))).trans M.ker_π

private lemma conjG₀_conj (M : S172DModel S B G₀ Ghat) {g : Γ}
    (hg : g ∈ Ghat) (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) :
    ∀ (b : ↥B) (s t : ↥S), (t : Ω) = (b : Ω)⁻¹ * s * b →
      (((conjG₀ g hgN).comp M.π) t : ↥G₀) =
        ((((conjGhat g hg).comp M.β) b : ↥Ghat) : Γ)⁻¹ *
          ((((conjG₀ g hgN).comp M.π) s : ↥G₀) : Γ) *
            (((conjGhat g hg).comp M.β) b : ↥Ghat) := by
  intro b s t ht
  have h := M.conj b s t ht
  show conjEnd g ((M.π t : ↥G₀) : Γ) =
    (conjEnd g ((M.β b : ↥Ghat) : Γ))⁻¹ * conjEnd g ((M.π s : ↥G₀) : Γ) *
      conjEnd g ((M.β b : ↥Ghat) : Γ)
  calc conjEnd g ((M.π t : ↥G₀) : Γ) =
      conjEnd g (((M.β b : ↥Ghat) : Γ)⁻¹ * ((M.π s : ↥G₀) : Γ) *
        ((M.β b : ↥Ghat) : Γ)) := by rw [h]
    _ = (conjEnd g ((M.β b : ↥Ghat) : Γ))⁻¹ * conjEnd g ((M.π s : ↥G₀) : Γ) *
          conjEnd g ((M.β b : ↥Ghat) : Γ) := by simp only [map_mul, map_inv]

private lemma conjModel_le (M : S172DModel S B G₀ Ghat) {g : Γ}
    (hg : g ∈ Ghat) (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) : G₀ ≤ Ghat := by
  intro y hy
  have h1 : g⁻¹ * (y : Γ) * g ∈ G₀ := conjEnd_inv_mem_G₀ hgN hy
  have h2 : g⁻¹ * (y : Γ) * g ∈ Ghat := M.le h1
  have e : (y : Γ) = g * (g⁻¹ * (y : Γ) * g) * g⁻¹ := by group
  rw [e]
  exact Ghat.mul_mem (Ghat.mul_mem hg h2) (Ghat.inv_mem hg)

private lemma conjModel_faithful (M : S172DModel S B G₀ Ghat) {g : Γ}
    (hg : g ∈ Ghat) (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) :
    ∀ x ∈ Ghat, (∀ y ∈ G₀, x * y = y * x) → x = 1 := by
  intro h hh hc
  have hh' : g⁻¹ * h * g ∈ Ghat :=
    Ghat.mul_mem (Ghat.mul_mem (Ghat.inv_mem hg) hh) hg
  have hc' : ∀ x ∈ G₀, (g⁻¹ * h * g) * x = x * (g⁻¹ * h * g) := by
    intro x hx
    have hx' : g * x * g⁻¹ ∈ G₀ := conjEnd_mem_G₀ hgN hx
    have h1 : h * (g * x * g⁻¹) = (g * x * g⁻¹) * h := hc (g * x * g⁻¹) hx'
    have e : (g⁻¹ * h * g) * x * (g⁻¹ * h * g)⁻¹ = x := by
      calc (g⁻¹ * h * g) * x * (g⁻¹ * h * g)⁻¹ =
          g⁻¹ * (h * (g * x * g⁻¹) * h⁻¹) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * h * h⁻¹) * g := by rw [h1]
        _ = x := by group
    calc (g⁻¹ * h * g) * x =
        ((g⁻¹ * h * g) * x * (g⁻¹ * h * g)⁻¹) * (g⁻¹ * h * g) := by group
      _ = x * (g⁻¹ * h * g) := by rw [e]
  have h1 : g⁻¹ * h * g = 1 := M.faithful _ hh' hc'
  have e : h = g * (g⁻¹ * h * g) * g⁻¹ := by group
  rw [e, h1]
  group

private def conjModel (M : S172DModel S B G₀ Ghat) {g : Γ} (hg : g ∈ Ghat)
    (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) : S172DModel S B G₀ Ghat where
  π := (conjG₀ g hgN).comp M.π
  β := (conjGhat g hg).comp M.β
  surj := conjG₀_surj M hgN
  ker_π := conjG₀_ker M hgN
  conj := conjG₀_conj M hg hgN
  le := conjModel_le M hg hgN
  faithful := conjModel_faithful M hg hgN

theorem exists_conj (M : S172DModel S B G₀ Ghat) {g : Γ} (hg : g ∈ Ghat)
    (hgN : g ∈ Subgroup.normalizer (G₀ : Set Γ)) :
    ∃ M' : S172DModel S B G₀ Ghat,
      M'.barB = M.barB.map (MulAut.conj g).toMonoidHom ∧
      (∀ X, M'.piImg X = (M.piImg X).map (MulAut.conj g).toMonoidHom) ∧
      ∀ X, M'.img X = (M.img X).map (MulAut.conj g).toMonoidHom := by
  refine ⟨conjModel M hg hgN, ?_, ?_, ?_⟩
  · show (((conjGhat g hg).comp M.β).range).map Ghat.subtype =
      ((M.β.range).map Ghat.subtype).map (MulAut.conj g).toMonoidHom
    rw [MonoidHom.range_comp]
    simp only [Subgroup.map_map]
    rfl
  · intro X
    show ((X.subgroupOf S).map ((conjG₀ g hgN).comp M.π)).map G₀.subtype =
      (((X.subgroupOf S).map M.π).map G₀.subtype).map (MulAut.conj g).toMonoidHom
    simp only [Subgroup.map_map]
    rfl
  · intro X
    show ((X.subgroupOf B).map ((conjGhat g hg).comp M.β)).map Ghat.subtype =
      (((X.subgroupOf B).map M.β).map Ghat.subtype).map (MulAut.conj g).toMonoidHom
    simp only [Subgroup.map_map]
    rfl

end S172DModel

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
