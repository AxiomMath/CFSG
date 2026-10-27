module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510
import CFSG.HardMathSupport.Timmesfeld.Proving.CoatomStep

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma510Ns
open scoped commutatorElement

section Layer

variable {Y : Type*} [Group Y]

theorem l3bf_glaPComponent_self {S : Subgroup Y} (hq : CFSG.Open.IsQuasisimple ↥S)
    (hO : GLAPPrimeCore 3 ↥S = ⊥) : GLAPComponent 3 S S := by
  have hker : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)).ker = ⊥ := by
    rw [QuotientGroup.ker_mk', hO]
  have hinj : Function.Injective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  have hL : (S.subgroupOf S).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S)) = ⊤ := by
    rw [Subgroup.subgroupOf_self, Subgroup.map_top, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  refine ⟨le_rfl, IsSubnormal.refl S, ⟨le_top, ?_, ?_⟩, ?_⟩
  · rw [hL]; exact IsSubnormal.refl _
  · rw [hL]
    let e : ↥S ≃* ↥(⊤ : Subgroup (↥S ⧸ GLAPPrimeCore 3 ↥S)) :=
      (MulEquiv.ofBijective (QuotientGroup.mk' (GLAPPrimeCore 3 ↥S))
        ⟨hinj, QuotientGroup.mk'_surjective _⟩).trans Subgroup.topEquiv.symm
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hq
  · intro J hJ _ h
    have h1 : J.subgroupOf S = S.subgroupOf S := Subgroup.map_injective hinj h
    rw [Subgroup.subgroupOf_self] at h1
    exact absurd (Subgroup.subgroupOf_eq_top.mp h1) (not_le_of_gt hJ)

variable [Finite Y]

theorem l3bf_layer_of_normal_perfect {F S : Subgroup Y} (hSF : S ≤ F)
    (hnorm : (S.subgroupOf F).Normal)
    (hperf : ∀ J : Subgroup Y, J ≤ F → ⁅J, J⁆ = J → J ≤ S)
    (hpow : ∀ a ∈ F, ∃ n : ℕ, a ^ 3 ^ n ∈ S) (hq : CFSG.Open.IsQuasisimple ↥S)
    (hO : GLAPPrimeCore 3 ↥S = ⊥) :
    GLAPPrimeCore 3 ↥F = ⊥ ∧ (∀ J : Subgroup Y, GLAPComponent 3 F J ↔ J = S) ∧
      GLAPLayer 3 F = S := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  have hOS : GLAPPrimeCoreOf 3 S = ⊥ := by
    rw [GLAPPrimeCoreOf, hO, Subgroup.map_bot]
  have hOF : GLAPPrimeCoreOf 3 F = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hyF : y ∈ F :=
      (CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.GLAPPrimeCoreOf_le 3 F) hy
    obtain ⟨n, hn⟩ := hpow y hyF
    have hyn : y ^ 3 ^ n ∈ GLAPPrimeCoreOf 3 F := Subgroup.pow_mem _ hy _
    have h1 : y ^ 3 ^ n ∈ GLAPPrimeCoreOf 3 (F ⊓ S) :=
      gLAPPrimeCoreOf_inf_le hp F S ⟨hyn, hn⟩
    rw [inf_eq_right.2 hSF, hOS, Subgroup.mem_bot] at h1
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCoreOf 3 F)) := by
      have h2 : Nat.card (GLAPPrimeCoreOf 3 F) = Nat.card (GLAPPrimeCore 3 ↥F) :=
        Subgroup.card_map_of_injective F.subtype_injective
      rw [h2]; exact coprime_card_gLAPPrimeCore_aux 3 ↥F
    have h3 : orderOf y ∣ Nat.card (GLAPPrimeCoreOf 3 F) :=
      Subgroup.orderOf_dvd_natCard (GLAPPrimeCoreOf 3 F) hy
    have h4 : orderOf y ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one h1
    have h5 : Nat.Coprime (orderOf y) (3 ^ n) :=
      Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left h3 hcop.symm)
    have h6 := Nat.Coprime.eq_one_of_dvd h5 h4
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 h6)
  have hOF' : GLAPPrimeCore 3 ↥F = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).1 hOF
  have hself := l3bf_glaPComponent_self hq hO
  have comp : ∀ J : Subgroup Y, GLAPComponent 3 F J ↔ J = S := by
    intro J
    constructor
    · intro hJ
      have hJF : J ≤ F := hJ.1
      have hJS : J ≤ S := hperf J hJF (glaPComponent_perfect hJ)
      have hsn : IsSubnormal J S := isSubnormal_of_le_of_le hJ.2.1 hJS hSF
      exact eq_of_isSubnormal_of_quasisimple hq hsn (glaPComponent_perfect hJ)
        (glaPComponent_ne_bot hJ)
    · rintro rfl
      exact glaPComponent_of_normal_sub hp hSF hnorm hself
  refine ⟨hOF', comp, le_antisymm (sSup_le fun A hA => ?_) (le_sSup ((comp S).2 rfl))⟩
  exact ((comp A).1 hA).le

end Layer

section Cover

theorem l3bf_center_eq_bot {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have : a ∈ Subgroup.center S := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem l3bf_quasisimple_of_cover {L S : Type*} [Group L] [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) (f : L →* S) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → x ∈ Subgroup.center L) (hperf : commutator L = ⊤) :
    CFSG.Open.IsQuasisimple L := by
  refine ⟨hperf, ?_⟩
  have hc : f.ker = Subgroup.center L := by
    apply le_antisymm
    · intro x hx
      exact hker x hx
    · intro x hx
      have h1 : f x ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨y, rfl⟩ := hf g
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx y]
      rw [l3bf_center_eq_bot hnab, Subgroup.mem_bot] at h1
      exact h1
  have e : L ⧸ Subgroup.center L ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hc.symm).trans (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact e.isSimpleGroup

theorem l3bf_primeCore_cover {L S : Type*} [Group L] [Finite L] [Group S] [IsSimpleGroup S]
    (h3 : 3 ∣ Nat.card S) (f : L →* S) (hf : Function.Surjective f)
    (hker : ∀ x, f x = 1 → ∃ n : ℕ, x ^ 3 ^ n = 1) : GLAPPrimeCore 3 L = ⊥ := by
  have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 L)) := coprime_card_gLAPPrimeCore_aux 3 L
  set M := GLAPPrimeCore 3 L with hM
  have hn : (M.map f).Normal := (inferInstance : M.Normal).map f hf
  have hbot : M.map f = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.map f) with h | h
    · exact h
    · exfalso
      have h1 : Nat.card (M.map f) ∣ Nat.card M := Subgroup.card_map_dvd M f
      rw [h, Subgroup.card_top] at h1
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_right (h3.trans h1) hcop) (dvd_refl 3))
        (by norm_num)
  rw [eq_bot_iff]
  intro x hx
  have hfx : f x = 1 := by
    have : f x ∈ M.map f := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  obtain ⟨n, hn3⟩ := hker x hfx
  have h3x : orderOf x ∣ Nat.card M := Subgroup.orderOf_dvd_natCard M hx
  have h4 : orderOf x ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn3
  have h5 : Nat.Coprime (orderOf x) (3 ^ n) :=
    Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left h3x hcop.symm)
  exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h5 h4))

end Cover

section Central

variable {Y H : Type*} [Group Y] [Group H]

theorem l3bf_commutator_central_mul {x y z w : Y} (hz : z ∈ Subgroup.center Y)
    (hw : w ∈ Subgroup.center Y) : ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have hw' := Subgroup.mem_center_iff.1 hw
  simp only [commutatorElement_def]
  calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
      = x * (z * (y * w) * z⁻¹) * x⁻¹ * (w⁻¹ * y⁻¹) := by group
    _ = x * (y * w) * x⁻¹ * (w⁻¹ * y⁻¹) := by rw [← hz' (y * w), mul_inv_cancel_right]
    _ = x * y * (w * x⁻¹ * w⁻¹) * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [← hw' x⁻¹, mul_inv_cancel_right]

theorem l3bf_commutator_le_of_map_le {π : Y →* H}
    (hker : ∀ y, π y = 1 → y ∈ Subgroup.center Y) {M M' : Subgroup Y}
    (h : M.map π ≤ M'.map π) : ⁅M, M⁆ ≤ ⁅M', M'⁆ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨a', ha', haa⟩ := h ⟨a, ha, rfl⟩
  obtain ⟨b', hb', hbb⟩ := h ⟨b, hb, rfl⟩
  have hza : a'⁻¹ * a ∈ Subgroup.center Y :=
    hker _ (by rw [map_mul, map_inv, haa, inv_mul_cancel])
  have hzb : b'⁻¹ * b ∈ Subgroup.center Y :=
    hker _ (by rw [map_mul, map_inv, hbb, inv_mul_cancel])
  have e : ⁅a, b⁆ = ⁅a', b'⁆ := by
    have := l3bf_commutator_central_mul (x := a') (y := b') hza hzb
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at this
  rw [e]
  exact Subgroup.commutator_mem_commutator ha' hb'

variable [Finite Y]

theorem l3bf_central_fixed {π : Y →* H} (hπ : Function.Surjective π)
    (hker : ∀ y, π y = 1 → y ∈ Subgroup.center Y)
    (hZ : ∀ z ∈ Subgroup.center Y, ∃ n : ℕ, z ^ 3 ^ n = 1)
    {α : MulAut Y} {ψ : MulAut H} (hc : ∀ y, π (α y) = ψ (π y))
    {C : Subgroup Y} (hC : ∀ y, y ∈ C ↔ α y = y)
    {D : Subgroup H} (hD : ∀ h, h ∈ D ↔ ψ h = h)
    {S : Subgroup H} (hSD : S ≤ D) [IsSimpleGroup ↥S] (hnab : ∃ a b : ↥S, a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card S) (hDS : ⁅D, D⁆ ≤ S) (hcube : ∀ d ∈ D, d ^ 3 ∈ S) :
    GLAPPrimeCore 3 ↥C = ⊥ ∧ ∃ L : Subgroup Y, L ≤ C ∧ CFSG.Open.IsQuasisimple ↥L ∧
      L.map π = S ∧ (∀ J : Subgroup Y, GLAPComponent 3 C J ↔ J = L) ∧ GLAPLayer 3 C = L := by
  have hSperf : ⁅S, S⁆ = S := by
    have h1 : (commutator ↥S).map S.subtype = ⁅S, S⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : commutator ↥S = ⊤ := by
      have : (commutator ↥S).Normal := inferInstance
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥S) with h | h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnab
        apply hab
        have : ⁅a, b⁆ ∈ commutator ↥S := by
          rw [commutator_def]; exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this
      · exact h
    rw [← h1, h2, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hCD : ∀ c ∈ C, π c ∈ D := fun c hc' => by
    rw [hD, ← hc, (hC c).1 hc']
  have hSC : S ≤ C.map π := by
    have : ⁅D, D⁆ ≤ C.map π := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨x, rfl⟩ := hπ a
      obtain ⟨y, rfl⟩ := hπ b
      have lift : ∀ t : Y, ψ (π t) = π t → t⁻¹ * α t ∈ Subgroup.center Y := fun t ht =>
        hker _ (by rw [map_mul, map_inv, hc, ht, inv_mul_cancel])
      have hx := lift x ((hD _).1 ha)
      have hy := lift y ((hD _).1 hb)
      refine ⟨⁅x, y⁆, ?_, by rw [map_commutatorElement]⟩
      rw [SetLike.mem_coe, hC]
      have e1 : α x = x * (x⁻¹ * α x) := by group
      have e2 : α y = y * (y⁻¹ * α y) := by group
      rw [map_commutatorElement, e1, e2, l3bf_commutator_central_mul hx hy]
    calc S = ⁅S, S⁆ := hSperf.symm
      _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hSD hSD
      _ ≤ C.map π := this
  set C₁ : Subgroup Y := C ⊓ S.comap π with hC₁
  set L : Subgroup Y := ⁅C₁, C₁⁆ with hL
  have hC₁S : C₁.map π = S := by
    apply le_antisymm
    · rintro _ ⟨c, hc', rfl⟩
      exact hc'.2
    · intro s hs
      obtain ⟨c, hcC, rfl⟩ := hSC hs
      exact ⟨c, ⟨hcC, hs⟩, rfl⟩
  have hLC : L ≤ C := by
    rw [hL, Subgroup.commutator_le]
    intro a ha b hb
    have ha' := (hC a).1 ha.1
    have hb' := (hC b).1 hb.1
    rw [hC, map_commutatorElement, ha', hb']
  have hLmap : L.map π = S := by rw [hL, Subgroup.map_commutator, hC₁S, hSperf]
  have hLperf : ⁅L, L⁆ = L := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
    · exact l3bf_commutator_le_of_map_le hker (by rw [hC₁S, hLmap])
  have hperfJ : ∀ J : Subgroup Y, J ≤ C → ⁅J, J⁆ = J → J ≤ L := by
    intro J hJC hJ
    have hJD : J.map π ≤ D := by
      rintro _ ⟨j, hj, rfl⟩
      exact hCD j (hJC hj)
    have hπJ : J.map π ≤ S := by
      calc J.map π = (⁅J, J⁆).map π := by rw [hJ]
        _ = ⁅J.map π, J.map π⁆ := Subgroup.map_commutator J J π
        _ ≤ ⁅D, D⁆ := Subgroup.commutator_mono hJD hJD
        _ ≤ S := hDS
    have hJC₁ : J ≤ C₁ := fun j hj => ⟨hJC hj, hπJ ⟨j, hj, rfl⟩⟩
    calc J = ⁅J, J⁆ := hJ.symm
      _ ≤ ⁅C₁, C₁⁆ := Subgroup.commutator_mono hJC₁ hJC₁
  have hSnormD : ∀ d ∈ D, ∀ s ∈ S, d * s * d⁻¹ ∈ S := by
    intro d hd s hs
    have h1 : ⁅d, s⁆ ∈ S := hDS (Subgroup.commutator_mem_commutator hd (hSD hs))
    have : d * s * d⁻¹ = ⁅d, s⁆ * s := by rw [commutatorElement_def]; group
    rw [this]
    exact S.mul_mem h1 hs
  have hC₁norm : ∀ g ∈ C, ∀ x ∈ C₁, g * x * g⁻¹ ∈ C₁ := by
    intro g hg x hx
    refine ⟨C.mul_mem (C.mul_mem hg hx.1) (C.inv_mem hg), ?_⟩
    show π (g * x * g⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv]
    exact hSnormD _ (hCD g hg) _ hx.2
  have hLnorm : (L.subgroupOf C).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLC]
    intro g hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have h1 : L.map (MulAut.conj g).toMonoidHom ≤ L := by
      rw [hL, Subgroup.map_commutator]
      apply Subgroup.commutator_mono <;>
      · rintro _ ⟨x, hx, rfl⟩
        exact hC₁norm g hg x hx
    exact h1 ⟨n, hn, rfl⟩
  have hf : ∀ l : ↥L, π l ∈ S := fun l => by
    have : π l ∈ L.map π := ⟨l, l.2, rfl⟩
    rwa [hLmap] at this
  let f' : ↥L →* ↥S := (π.comp L.subtype).codRestrict S hf
  have hf's : Function.Surjective f' := by
    intro s
    have : (s : H) ∈ L.map π := by rw [hLmap]; exact s.2
    obtain ⟨l, hl, hls⟩ := this
    exact ⟨⟨l, hl⟩, Subtype.ext hls⟩
  have hf'ker : ∀ x, f' x = 1 → x ∈ Subgroup.center ↥L := by
    intro x hx
    have h1 : π x = 1 := congrArg Subtype.val hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.1 (hker _ h1) g))
  have hLq : CFSG.Open.IsQuasisimple ↥L := by
    refine l3bf_quasisimple_of_cover hnab f' hf's hf'ker ?_
    have h1 : (commutator ↥L).map L.subtype = ⁅L, L⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have h2 : (⊤ : Subgroup ↥L).map L.subtype = L := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective L.subtype_injective (h1.trans (hLperf.trans h2.symm))
  have hLO : GLAPPrimeCore 3 ↥L = ⊥ := by
    refine l3bf_primeCore_cover h3 f' hf's ?_
    intro x hx
    obtain ⟨n, hn⟩ := hZ _ (hker _ (congrArg Subtype.val hx))
    exact ⟨n, Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hn)⟩
  have hpow : ∀ a ∈ C, ∃ n : ℕ, a ^ 3 ^ n ∈ L := by
    intro a ha
    have ha3 : a ^ 3 ∈ C := C.pow_mem ha 3
    have hπ3 : π (a ^ 3) ∈ S := by rw [map_pow]; exact hcube _ (hCD a ha)
    have : π (a ^ 3) ∈ L.map π := by rw [hLmap]; exact hπ3
    obtain ⟨l, hl, hle⟩ := this
    have hz : l⁻¹ * a ^ 3 ∈ Subgroup.center Y :=
      hker _ (by rw [map_mul, map_inv, hle, inv_mul_cancel])
    obtain ⟨n, hn⟩ := hZ _ hz
    refine ⟨n + 1, ?_⟩
    have hcomm : Commute l (l⁻¹ * a ^ 3) := by
      have := Subgroup.mem_center_iff.1 hz l
      exact this
    have e : a ^ 3 = l * (l⁻¹ * a ^ 3) := by group
    have : a ^ 3 ^ (n + 1) = (a ^ 3) ^ 3 ^ n := by rw [pow_succ, mul_comm, pow_mul]
    rw [this, e, hcomm.mul_pow, hn, mul_one]
    exact L.pow_mem hl _
  obtain ⟨hOC, hcomp, hlay⟩ := l3bf_layer_of_normal_perfect hLC hLnorm hperfJ hpow hLq hLO
  exact ⟨hOC, L, hLC, hLq, hLmap, hcomp, hlay⟩

end Central

section FixData

variable {P : Type*} [Group P]

@[expose] def l3bFix (φ : MulAut P) : Subgroup P where
  carrier := {x | φ x = x}
  mul_mem' := fun {a b} ha hb => by
    show φ (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := map_one φ
  inv_mem' := fun {a} ha => by
    show φ a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

theorem mem_l3bFix {φ : MulAut P} {x : P} : x ∈ l3bFix φ ↔ φ x = x := Iff.rfl

structure L3BFixData (φ : MulAut P) : Prop where
  simple : IsSimpleGroup ↥⁅l3bFix φ, l3bFix φ⁆
  nonab : ∃ a b : ↥⁅l3bFix φ, l3bFix φ⁆, a * b ≠ b * a
  three_dvd : 3 ∣ Nat.card ↥⁅l3bFix φ, l3bFix φ⁆
  cube : ∀ d ∈ l3bFix φ, d ^ 3 ∈ ⁅l3bFix φ, l3bFix φ⁆

theorem l3bFix_conj (φ γ : MulAut P) :
    l3bFix (γ * φ * γ⁻¹) = (l3bFix φ).map γ.toMonoidHom := by
  ext x
  constructor
  · intro hx
    refine ⟨γ⁻¹ x, ?_, by simp⟩
    have : (γ * φ * γ⁻¹) x = x := hx
    simp only [MulAut.mul_apply, MulAut.inv_apply] at this
    show φ (γ.symm x) = γ.symm x
    apply γ.injective
    rw [this]
    simp
  · rintro ⟨y, hy, rfl⟩
    show (γ * φ * γ⁻¹) (γ y) = γ y
    simp only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact congrArg γ hy

theorem L3BFixData.conj {φ : MulAut P} (h : L3BFixData φ) (γ : MulAut P) :
    L3BFixData (γ * φ * γ⁻¹) := by
  have hD := l3bFix_conj φ γ
  have hC : ⁅l3bFix (γ * φ * γ⁻¹), l3bFix (γ * φ * γ⁻¹)⁆ =
      (⁅l3bFix φ, l3bFix φ⁆).map γ.toMonoidHom := by
    rw [hD, Subgroup.map_commutator]
  let e := (⁅l3bFix φ, l3bFix φ⁆).equivMapOfInjective γ.toMonoidHom γ.injective
  let e' := MulEquiv.subgroupCongr hC.symm
  let E := e.trans e'
  have hs := h.simple
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact E.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := h.nonab
    refine ⟨E a, E b, fun hc => hab (E.injective ?_)⟩
    rw [map_mul, map_mul]
    exact hc
  · rw [Nat.card_congr E.symm.toEquiv]
    exact h.three_dvd
  · intro d hd
    rw [hD] at hd
    obtain ⟨d₀, hd₀, rfl⟩ := hd
    rw [hC]
    exact ⟨d₀ ^ 3, h.cube d₀ hd₀, by simp⟩

theorem l3bf_perfect_eq_bot_of_solvable {G : Type*} [Group G] {J D : Subgroup G} (hJD : J ≤ D)
    (hs : Group.IsSolvable ↥D) (hp : ⁅J, J⁆ = J) : J = ⊥ := by
  have : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJD)
  by_contra hne
  have hnt : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).2 hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥J
  have h2 : commutator ↥J = ⊤ := by
    have e1 : (commutator ↥J).map J.subtype = ⁅J, J⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have e2 : (⊤ : Subgroup ↥J).map J.subtype = J := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact Subgroup.map_injective J.subtype_injective (e1.trans (hp.trans e2.symm))
  exact lt_irrefl _ (h2 ▸ h1)

theorem l3bf_solvable_of_commutator_le {P : Type*} [Group P] {D T : Subgroup P}
    (hT : Group.IsSolvable ↥T) (h : ⁅D, D⁆ ≤ T) : Group.IsSolvable ↥D := by
  have hmap : (commutator ↥D).map D.subtype = ⁅D, D⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hN : Group.IsSolvable ↥(commutator ↥D) := by
    let f : ↥(commutator ↥D) →* ↥T :=
      { toFun := fun x => ⟨((x : ↥D) : P), h (hmap ▸ ⟨x, x.2, rfl⟩)⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    exact Group.isSolvable_of_isSolvable_injective (f := f) (fun x y hxy =>
      Subtype.ext (Subtype.ext (congrArg (fun t : ↥T => (t : P)) hxy)))
  have hq : Group.IsSolvable (↥D ⧸ commutator ↥D) := by
    apply Group.isSolvable_of_comm
    intro a b
    induction a using QuotientGroup.induction_on with
    | H a =>
      induction b using QuotientGroup.induction_on with
      | H b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        have : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by rw [commutatorElement_def]; group
        rw [this]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  exact Group.isSolvable_of_subgroup_quotient (commutator ↥D)

end FixData

section Solvable

variable {Y H : Type*} [Group Y] [Group H]

theorem l3bf_layer_bot {π : Y →* H} (hker : ∀ y, π y = 1 → y ∈ Subgroup.center Y)
    {α : MulAut Y} {ψ : MulAut H} (hc : ∀ y, π (α y) = ψ (π y))
    {C : Subgroup Y} (hC : ∀ y, y ∈ C ↔ α y = y) (hs : Group.IsSolvable ↥(l3bFix ψ)) :
    GLAPLayer 3 C = ⊥ := by
  rw [GLAPLayer, eq_bot_iff]
  refine sSup_le fun J hJ => ?_
  have hJC : J ≤ C := hJ.1
  have hperf := glaPComponent_perfect hJ
  have hJD : J.map π ≤ l3bFix ψ := by
    rintro _ ⟨j, hj, rfl⟩
    show ψ (π j) = π j
    rw [← hc, (hC j).1 (hJC hj)]
  have h1 : ⁅J.map π, J.map π⁆ = J.map π := by
    rw [← Subgroup.map_commutator, hperf]
  have h2 := l3bf_perfect_eq_bot_of_solvable hJD hs h1
  have hJZ : J ≤ Subgroup.center Y := by
    intro j hj
    apply hker
    have : π j ∈ J.map π := ⟨j, hj, rfl⟩
    rw [h2, Subgroup.mem_bot] at this
    exact this
  have h3 : ⁅J, J⁆ = ⊥ := by
    rw [Subgroup.commutator_le.2 ?_ |> fun h => eq_bot_iff.2 h]
    intro a ha b hb
    rw [commutatorElement_def, Subgroup.mem_bot]
    have := Subgroup.mem_center_iff.1 (hJZ ha) b
    rw [mul_assoc, ← this]
    group
  exact (glaPComponent_ne_bot hJ (hperf ▸ h3)).elim

variable [Finite Y]

theorem l3bf_core_of_fixed_core {π : Y →* H} (hπ : Function.Surjective π)
    (hker : ∀ y, π y = 1 → y ∈ Subgroup.center Y)
    (hZ : ∀ z ∈ Subgroup.center Y, ∃ n : ℕ, z ^ 3 ^ n = 1)
    {α : MulAut Y} {ψ : MulAut H} (hc : ∀ y, π (α y) = ψ (π y))
    {C : Subgroup Y} (hC : ∀ y, y ∈ C ↔ α y = y)
    (hD : GLAPPrimeCore 3 ↥(l3bFix ψ) = ⊥) : GLAPPrimeCore 3 ↥C = ⊥ := by
  have hp : (3 : ℕ).Prime := Nat.prime_three
  set N := GLAPPrimeCoreOf 3 C with hN
  have hNC : N ≤ C := CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreOf_le (p := 3) C
  have hCD : ∀ c ∈ C, π c ∈ l3bFix ψ := fun c hc' => by
    show ψ (π c) = π c
    rw [← hc, (hC c).1 hc']
  have hnorm : ∀ y : Y, π y ∈ l3bFix ψ → y ∈ Subgroup.normalizer (C : Set Y) := by
    have key : ∀ y : Y, π y ∈ l3bFix ψ → ∀ c ∈ C, y * c * y⁻¹ ∈ C := by
      intro y hy c hcC
      have hz : y⁻¹ * α y ∈ Subgroup.center Y :=
        hker _ (by rw [map_mul, map_inv, hc, hy, inv_mul_cancel])
      have e1 : α y = y * (y⁻¹ * α y) := by group
      rw [hC, map_mul, map_mul, map_inv, e1, (hC c).1 hcC]
      have := Subgroup.mem_center_iff.1 hz
      calc y * (y⁻¹ * α y) * c * (y * (y⁻¹ * α y))⁻¹ = y * ((y⁻¹ * α y) * c * (y⁻¹ * α y)⁻¹) * y⁻¹ := by
            group
        _ = y * c * y⁻¹ := by rw [← this c, mul_inv_cancel_right]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key y hy h hh, fun hh => ?_⟩
    have hy' : π y⁻¹ ∈ l3bFix ψ := by rw [map_inv]; exact (l3bFix ψ).inv_mem hy
    have h2 := key y⁻¹ hy' _ hh
    have e : y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ = h := by group
    rw [e] at h2
    exact h2
  have hM : N.map π ≤ GLAPPrimeCoreOf 3 (l3bFix ψ) := by
    apply CFSG.HardMathSupport.Timmesfeld.Proving.le_GLAPPrimeCoreOf_of_normal
    · rintro _ ⟨n, hn, rfl⟩
      exact hCD n (hNC hn)
    · rintro g hg _ ⟨n, hn, rfl⟩
      obtain ⟨y, rfl⟩ := hπ g
      have hyn := CFSG.HardMathSupport.Timmesfeld.Proving.normalizer_GLAPPrimeCoreOf (p := 3) hp (hnorm y hg)
      refine ⟨y * n * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.1 hyn n).1 hn
    · exact Nat.Coprime.coprime_dvd_right
        (by
          have := Subgroup.card_map_dvd N π
          exact this)
        (CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp C)
  have hDbot : GLAPPrimeCoreOf 3 (l3bFix ψ) = ⊥ := by rw [GLAPPrimeCoreOf, hD, Subgroup.map_bot]
  rw [hDbot] at hM
  have hNz : N ≤ ⊥ := by
    intro n hn
    have h1 : π n = 1 := by
      have : π n ∈ N.map π := ⟨n, hn, rfl⟩
      have := hM this
      rwa [Subgroup.mem_bot] at this
    obtain ⟨k, hk⟩ := hZ n (hker n h1)
    have hcop := CFSG.HardMathSupport.Timmesfeld.Proving.coprime_card_GLAPPrimeCoreOf hp C
    have h3 : orderOf n ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N hn
    have h4 : orderOf n ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have h5 : Nat.Coprime (orderOf n) (3 ^ k) :=
      Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h3 hcop.symm)
    exact Subgroup.mem_bot.2 (orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h5 h4))
  have hNb : GLAPPrimeCoreOf 3 C = ⊥ := le_bot_iff.1 hNz
  exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 hNb

end Solvable


end CFSG.HardMathSupport.Solomon.Coordinator
