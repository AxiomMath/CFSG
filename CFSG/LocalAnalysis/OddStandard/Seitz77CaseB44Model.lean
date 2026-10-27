module

public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Loc
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Qmax
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Root
public import CFSG.LocalAnalysis.OddStandard.Seitz77CaseB44Weyl

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Open CFSG.Blueprint CFSG.ABGLocalTools CFSG.OddStandard.Seitz77.CaseB45
  CFSG.RankThreeCoreUniqueness.Helpers CFSG.LocalAnalysis.ComponentInitial.FieldFourCover
open scoped commutatorElement

section Generic

theorem nonempty_centerQuotient_equiv {K L : Type*} [Group K] [Group L]
    (hK : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (ψ : K →* L) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center K) :
    Nonempty (K ⧸ Subgroup.center K ≃* L ⧸ Subgroup.center L) := by
  have hcenter : Subgroup.center K = ((QuotientGroup.mk' (Subgroup.center L)).comp ψ).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro l
      obtain ⟨y, rfl⟩ := hψ l
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hx y]
    · intro hx
      refine mem_center_of_commutator_mem_center hK fun y => hker ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (Subgroup.mem_center_iff.mp hx (ψ y)).symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcenter).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hψ))⟩

theorem commutator_self_eq_of_commutator_eq_top {G : Type*} [Group G] {A : Subgroup G}
    (h : commutator ↥A = ⊤) : ⁅A, A⁆ = A := by
  have h1 : ⁅(⊤ : Subgroup ↥A), (⊤ : Subgroup ↥A)⁆ = ⊤ := by
    rw [← commutator_def]; exact h
  have h2 := congrArg (Subgroup.map A.subtype) h1
  rw [Subgroup.map_commutator] at h2
  have h3 : (⊤ : Subgroup ↥A).map A.subtype = A := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rwa [h3] at h2

theorem commutator_top_of_perfect {G : Type*} [Group G] {H : Subgroup G} (h : ⁅H, H⁆ = H) :
    ⁅(⊤ : Subgroup ↥H), (⊤ : Subgroup ↥H)⁆ = ⊤ := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_commutator]
  have h3 : (⊤ : Subgroup ↥H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h3, h]

end Generic

section Side

variable {G : Type} [Group G] [Finite G] {A R : Subgroup G} {t : G} {c : CaseB A R t}
  {M M' S A₁ B₁ : Subgroup G} (Sd : Side c M M' S A₁ B₁)

include Sd

theorem Side.dg_comm_t' {m : G} (hm : m ∈ M) :
    (m * (t * m * t⁻¹)) * t = t * (m * (t * m * t⁻¹)) := by
  have h1 : t * (m * (t * m * t⁻¹)) * t⁻¹ = (t * m * t⁻¹) * m := by
    calc t * (m * (t * m * t⁻¹)) * t⁻¹ = (t * m * t⁻¹) * (t * (t * m * t⁻¹) * t⁻¹) := by group
      _ = (t * m * t⁻¹) * m := by rw [Sd.P.conj_conj]
  have h2 : (t * m * t⁻¹) * m = m * (t * m * t⁻¹) :=
    (Sd.F.comm_elem Sd.hZ hm (Sd.F.swap₁ m hm)).symm
  calc (m * (t * m * t⁻¹)) * t = (t * (m * (t * m * t⁻¹)) * t⁻¹) * t := by rw [h1, h2]
    _ = t * (m * (t * m * t⁻¹)) := by group

theorem Side.dg_mem {A' : Subgroup G} (hVd : ∀ a ∈ A₁, a * (t * a * t⁻¹) ∈ A')
    (hN : ∀ x : G, x * t = t * x → x ∈ normalizer (A' : Set G)) :
    ∀ m ∈ M, m * (t * m * t⁻¹) ∈ A' := by
  intro m hm
  have hgen := perfect_le_closure_conj_sylow Sd.F.perfect₁ Sd.sylow hm
  refine (Subgroup.closure_induction (p := fun x _ => x ∈ M ∧ x * (t * x * t⁻¹) ∈ A') ?_ ?_ ?_ ?_
    hgen).2
  · rintro _ ⟨m', hm', s, hs, rfl⟩
    have hsM : s ∈ M := Sd.A₁_le hs
    refine ⟨M.mul_mem (M.mul_mem hm' hsM) (M.inv_mem hm'), ?_⟩
    rw [← Sd.dg_conj hm' hsM]
    have hn := mem_normalizer_iff.mp (hN _ (Sd.dg_comm_t' hm')) (s * (t * s * t⁻¹))
    exact hn.mp (hVd s hs)
  · exact ⟨M.one_mem, by simp⟩
  · rintro x y - - ⟨hx, hxA⟩ ⟨hy, hyA⟩
    refine ⟨M.mul_mem hx hy, ?_⟩
    rw [Sd.F.diag_mul Sd.hZ hx hy]
    exact A'.mul_mem hxA hyA
  · rintro x - ⟨hx, hxA⟩
    refine ⟨M.inv_mem hx, ?_⟩
    rw [← Sd.dg_inv hx]
    exact A'.inv_mem hxA

end Side

section CS

variable {G : Type} [Group G] [Finite G] {A V₁ V₂ : Subgroup G} {d : Datum A}
  {c₁ : CaseB A V₁ d.t} {c₂ : CaseB A V₂ d.t} {M₁ M₂ N₁ N₂ S A₁ B₁ : Subgroup G} {k : Type}
  [Field k] {e : ↥A₁ ≃* ↥(unipAll k)} (CS : CommonSylow c₁ c₂ M₁ M₂ N₁ N₂ S A₁ B₁ e)

include CS

theorem CommonSylow.model_of_comm (h : Hyp G A) (hZ₁ : c₁.OddCoreCentral)
    (hZ₂ : c₂.OddCoreCentral) {σa σb : G} {Up Uq : Subgroup G}
    (W : WeylInput A d.V V₁ V₂ σa σb Up Uq) (hcomm : ⁅M₁ ⊔ N₁, M₂ ⊔ N₂⁆ = ⊥) :
    LieModel ((M₁ ⊔ N₁ : Subgroup G) ⧸ center (M₁ ⊔ N₁ : Subgroup G)) .PSL 3 2 2 := by
  have S₁ := CS.side₁ hZ₁
  have S₂ := CS.side₂ hZ₂
  have P := CS.swapPair
  have ht : d.t * d.t = 1 := c₁.t_mul_self
  have hG₂ : cs d.t (M₁ ⊔ N₁) = M₂ ⊔ N₂ := by rw [cs_sup, ← CS.M₂_eq, ← CS.N₂_eq]
  have hc : ∀ x ∈ M₁ ⊔ N₁, ∀ y ∈ M₁ ⊔ N₁, x * (d.t * y * d.t⁻¹) = (d.t * y * d.t⁻¹) * x := by
    intro x hx y hy
    have hy' : d.t * y * d.t⁻¹ ∈ M₂ ⊔ N₂ := hG₂ ▸ mem_cs_iff.mpr hy
    have := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact (mem_centralizer_iff.mp this _ hy').symm
  have hmulδ : ∀ y z : G, y ∈ M₁ ⊔ N₁ → z ∈ M₁ ⊔ N₁ →
      (y * z) * (d.t * (y * z) * d.t⁻¹) = (y * (d.t * y * d.t⁻¹)) * (z * (d.t * z * d.t⁻¹)) := by
    intro y z hy hz
    have h1 := hc z hz y hy
    calc (y * z) * (d.t * (y * z) * d.t⁻¹)
        = y * (z * (d.t * y * d.t⁻¹)) * (d.t * z * d.t⁻¹) := by group
      _ = y * ((d.t * y * d.t⁻¹) * z) * (d.t * z * d.t⁻¹) := by rw [h1]
      _ = (y * (d.t * y * d.t⁻¹)) * (z * (d.t * z * d.t⁻¹)) := by group
  let δ : ↥(M₁ ⊔ N₁) →* G :=
    { toFun := fun x => (x : G) * (d.t * (x : G) * d.t⁻¹)
      map_one' := by simp
      map_mul' := fun x y => hmulδ x y x.2 y.2 }
  have hδ : ∀ x : ↥(M₁ ⊔ N₁), δ x = (x : G) * (d.t * (x : G) * d.t⁻¹) := fun x => rfl
  have hVd : ∀ a ∈ A₁, a * (d.t * a * d.t⁻¹) ∈ A := fun a ha =>
    ((CS.syl.V_diag _).mpr ⟨a, ha, rfl⟩).2
  have hN : ∀ x : G, x * d.t = d.t * x → x ∈ normalizer (A : Set G) := fun x hx =>
    (centralizer_t_facts d.sector).1 (mem_centralizer_singleton_iff.mpr hx)
  have hδA : ∀ x : ↥(M₁ ⊔ N₁), δ x ∈ A := by
    intro x
    have key : ∀ y ∈ M₁ ⊔ N₁, y * (d.t * y * d.t⁻¹) ∈ A := by
      intro y hy
      have hy' : y ∈ Subgroup.closure ((M₁ : Set G) ∪ (N₁ : Set G)) := by
        rw [← Subgroup.sup_eq_closure]; exact hy
      refine (Subgroup.closure_induction
        (p := fun y _ => y ∈ M₁ ⊔ N₁ ∧ y * (d.t * y * d.t⁻¹) ∈ A) ?_ ?_ ?_ ?_ hy').2
      · rintro y (hy | hy)
        · exact ⟨Subgroup.mem_sup_left hy, S₁.dg_mem hVd hN y hy⟩
        · exact ⟨Subgroup.mem_sup_right hy, S₂.dg_mem hVd hN y hy⟩
      · exact ⟨one_mem _, by simp⟩
      · rintro y z - - ⟨hy, hyA⟩ ⟨hz, hzA⟩
        exact ⟨mul_mem hy hz, by rw [hmulδ y z hy hz]; exact A.mul_mem hyA hzA⟩
      · rintro y - ⟨hy, hyA⟩
        refine ⟨inv_mem hy, ?_⟩
        have h1 := hmulδ y y⁻¹ hy (inv_mem hy)
        rw [mul_inv_cancel, show d.t * (1 : G) * d.t⁻¹ = 1 by group, mul_one] at h1
        have h2 : y⁻¹ * (d.t * y⁻¹ * d.t⁻¹) = (y * (d.t * y * d.t⁻¹))⁻¹ :=
          (eq_inv_of_mul_eq_one_right h1.symm)
        rw [h2]
        exact A.inv_mem hyA
    exact key x x.2
  let δ' : ↥(M₁ ⊔ N₁) →* ↥A := δ.codRestrict A hδA
  have hδ'val : ∀ x, ((δ' x : ↥A) : G) = δ x := fun x => rfl
  have hDA : δ.range ≤ A := by
    rintro _ ⟨x, rfl⟩
    exact hδA x
  have hσaN : σa ∈ c₁.Ninf := perfectResidualOf_mono c₁.normalizer_A_R_le_N W.σa_mem
  have hσbN : σb ∈ c₂.Ninf := perfectResidualOf_mono c₂.normalizer_A_R_le_N W.σb_mem
  have hσaA : σa ∈ A := (perfectResidualOf_le' _ W.σa_mem).1
  have hσbA : σb ∈ A := (perfectResidualOf_le' _ W.σb_mem).1
  obtain ⟨m, hm, hσam⟩ := CS.F₁.exists_diag hZ₁ hσaN (d.comm_t_of_mem hσaA)
  obtain ⟨n, hn, hσbn⟩ := CS.F₂.exists_diag hZ₂ hσbN (d.comm_t_of_mem hσbA)
  have hVD : d.V ≤ δ.range := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := (CS.syl.V_diag v).mp hv
    exact ⟨⟨a, Subgroup.mem_sup_left (CS.A₁_le_M₁ ha)⟩, rfl⟩
  have hσaD : σa ∈ δ.range := ⟨⟨m, Subgroup.mem_sup_left hm⟩, hσam.symm⟩
  have hσbD : σb ∈ δ.range := ⟨⟨n, Subgroup.mem_sup_right hn⟩, hσbn.symm⟩
  have hperf : ⁅A, A⁆ = A := commutator_self_eq_of_commutator_eq_top h.commutator_eq_top
  have hAD : A ≤ δ.range := by
    have hVσ : d.V ⊔ zpowers σa ⊔ zpowers σb ≤ δ.range :=
      sup_le (sup_le hVD (Subgroup.zpowers_le.mpr hσaD)) (Subgroup.zpowers_le.mpr hσbD)
    rw [← hperf]
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hcz : ∀ u ∈ δ.range, ∀ z ∈ A ⊓ centralizer (A : Set G), u * z = z * u :=
      fun u hu z hz => mem_centralizer_iff.mp hz.2 u (hDA hu)
    obtain ⟨d₁, hd₁, z₁, hz₁, rfl⟩ := mem_sup_of_forall_comm (O := δ.range)
      (E := A ⊓ centralizer (A : Set G)) hcz (sup_le_sup_right hVσ _ (W.gen hx))
    obtain ⟨d₂, hd₂, z₂, hz₂, rfl⟩ := mem_sup_of_forall_comm (O := δ.range)
      (E := A ⊓ centralizer (A : Set G)) hcz (sup_le_sup_right hVσ _ (W.gen hy))
    have hz₁₂ : ⁅z₁, z₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_iff.mp hz₁.2 z₂ hz₂.1).symm
    rw [commutator_mul_of_comm (hcz d₁ hd₁ z₁ hz₁).symm.symm.symm (hcz d₂ hd₂ z₁ hz₁).symm
      (hcz d₁ hd₁ z₂ hz₂).symm (hcz d₂ hd₂ z₂ hz₂).symm, hz₁₂, mul_one, commutatorElement_def]
    exact δ.range.mul_mem (δ.range.mul_mem (δ.range.mul_mem hd₁ hd₂) (δ.range.inv_mem hd₁))
      (δ.range.inv_mem hd₂)
  have hsurj : Function.Surjective δ' := by
    intro x
    obtain ⟨y, hy⟩ := hAD x.2
    exact ⟨y, Subtype.ext hy⟩
  have hker : δ'.ker ≤ center ↥(M₁ ⊔ N₁) := by
    intro x hx
    have hx1 : δ x = 1 := by
      have h0 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rw [hδ'val] at h0
      exact h0
    rw [hδ] at hx1
    have hxinv : d.t * (x : G) * d.t⁻¹ = (x : G)⁻¹ := eq_inv_of_mul_eq_one_right hx1
    have hxG₂ : (x : G) ∈ M₂ ⊔ N₂ := by
      rw [← hG₂, mem_cs]
      have e : d.t⁻¹ * (x : G) * d.t = d.t * (x : G) * d.t⁻¹ := by
        have : d.t⁻¹ = d.t := inv_eq_of_mul_eq_one_right ht
        rw [this]
      rw [e, hxinv]
      exact inv_mem x.2
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm g.2
    exact Subtype.ext (mem_centralizer_iff.mp hg _ hxG₂).symm
  have hK : ⁅(⊤ : Subgroup ↥(M₁ ⊔ N₁)), (⊤ : Subgroup ↥(M₁ ⊔ N₁))⁆ = ⊤ :=
    commutator_top_of_perfect (perfect_sup CS.F₁.perfect₁ CS.F₂.perfect₁)
  obtain ⟨E⟩ := nonempty_centerQuotient_equiv hK δ' hsurj hker
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv E.symm h.model

end CS

end CFSG.OddStandard.Seitz77
