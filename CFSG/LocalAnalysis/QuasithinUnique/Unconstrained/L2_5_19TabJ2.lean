module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19TabBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdTabEmbed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115SporadicJ2
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverExternal
public import CFSG.LocalAnalysis.ComponentClassification.M12J2CoverDisplacement
public import CFSG.Sporadic.SmallOddCore.GroupFacts

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.Schreier
open scoped commutatorElement

section Model

open CFSG.ComponentClassification.J2Cover

theorem j2_inner_centralizer_card
    (t : Equiv.Perm (Fin 315)) (ht : t ∈ P) (ho : orderOf t = 2) :
    Nat.card (centralizerIn P t) = 240 ∨ Nat.card (centralizerIn P t) = 1920 := by
  obtain ⟨hcov, -, he1, -, he2⟩ := inner_classes
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov t ht ho
  rw [centralizerIn_conj P hc r, Subgroup.card_map_of_injective (MulAut.conj c).injective]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · left
    rw [he1]
    exact cent2B_facts.2.1
  · right
    rw [he2]
    exact cent2A_facts.2.1

theorem j2_fixSub_card
    (α : MulAut P) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    Nat.card (fixSub α) = 240 ∨ Nat.card (fixSub α) = 336 ∨ Nat.card (fixSub α) = 1920 := by
  by_cases hin : α ∈ inner P
  · obtain ⟨s, rfl⟩ := hin
    have hs : ∀ h : P, ((MulAut.conj s h : P) : Equiv.Perm (Fin 315)) =
        (s : Equiv.Perm (Fin 315)) * h * (s : Equiv.Perm (Fin 315))⁻¹ := by
      intro h
      simp [MulAut.conj_apply]
    have hmap := map_fixSub_conjOn P (MulAut.conj s) (s : Equiv.Perm (Fin 315)) hs
    have hcard : Nat.card (fixSub (MulAut.conj s)) =
        Nat.card (centralizerIn P (s : Equiv.Perm (Fin 315))) := by
      rw [← hmap, Subgroup.card_map_of_injective P.subtype_injective]
    have hss : s * s = 1 := by
      have hc : s * s ∈ Subgroup.center P := by
        rw [Subgroup.mem_center_iff]
        intro z
        have hz := congrArg (fun φ : MulAut P => φ z) hα2
        simp only [MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply] at hz
        calc z * (s * s) = (s * (s * z * s⁻¹) * s⁻¹) * (s * s) := by rw [hz]
          _ = (s * s) * z := by group
      rw [center_P, Subgroup.mem_bot] at hc
      exact hc
    have hs1 : s ≠ 1 := by
      rintro rfl
      exact hα1 (by ext z; simp)
    have ho : orderOf (s : Equiv.Perm (Fin 315)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (by rw [sq]; exact hss) hs1
    rw [hcard]
    rcases j2_inner_centralizer_card _ s.2 ho with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · right
    left
    have := CFSG.QuasithinUnique.Ch1.j2_outer_fixSub_card α hα2 hin
    simpa using this

theorem j2_outer_conj
    (α : MulAut P) (hα2 : α * α = 1) (hα : α ∉ inner P) :
    ∃ w : Equiv.Perm (Fin 315), permU⁻¹ * w ∈ P ∧ orderOf w = 2 ∧
      ∀ h : P, ((α h : P) : Equiv.Perm (Fin 315)) = w * h * w⁻¹ := by
  have hδ : ∀ h ∈ P, permU * h * permU⁻¹ ∈ P := permU_conj_mem
  have hδ2 : permU * permU ∈ P := by
    rw [permU_mul_self]
    exact P.one_mem
  have hδ' := inv_conj_mem P hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer P permU hδ hδ2 center_P permU_outer
    (by rw [card_mulAut_P, card_P]) α hα
  set u := g * permU with hu_def
  have hu : permU⁻¹ * u ∈ P := by simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ P := by
    have : u * u = g * (permU * g * permU⁻¹) * (permU * permU) := by simp only [u]; group
    rw [this]
    exact P.mul_mem (P.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : P) ∈ Subgroup.center P := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut P => (φ z : Equiv.Perm (Fin 315))) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : Equiv.Perm (Fin 315)) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [center_P, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  exact ⟨u, hu, orderOf_eq_prime (by rw [sq]; exact hu2) hu1, hαg⟩

theorem j2_outer_fusion
    {w : Equiv.Perm (Fin 315)} (hw : permU⁻¹ * w ∈ P) (hw2 : orderOf w = 2)
    {v : Equiv.Perm (Fin 315)} (hv : v ∈ P) (hvw : v * w = w * v) (hv2 : v * v = 1) :
    ∃ x ∈ P, x⁻¹ * w * x = w * v := by
  by_cases hv1 : v = 1
  · exact ⟨1, P.one_mem, by simp [hv1]⟩
  · have hww : w * w = 1 := by
      rw [← sq]
      have := pow_orderOf_eq_one w
      rwa [hw2] at this
    have hw' : permU⁻¹ * (w * v) ∈ P := by
      rw [← mul_assoc]
      exact P.mul_mem hw hv
    have hwv2 : (w * v) * (w * v) = 1 := by
      calc (w * v) * (w * v) = w * (v * w) * v := by group
        _ = w * (w * v) * v := by rw [hvw]
        _ = (w * w) * (v * v) := by group
        _ = 1 := by rw [hww, hv2, mul_one]
    have hwv1 : w * v ≠ 1 := by
      intro h
      apply permU_not_mem
      have hwP : w ∈ P := by
        have : w = v⁻¹ := eq_inv_of_mul_eq_one_left h
        rw [this]
        exact P.inv_mem hv
      have h1 : permU⁻¹ = (permU⁻¹ * w) * w⁻¹ := by group
      have h2 : permU⁻¹ ∈ P := by
        rw [h1]
        exact P.mul_mem hw (P.inv_mem hwP)
      simpa using P.inv_mem h2
    have ho' : orderOf (w * v) = 2 := orderOf_eq_prime (by rw [sq]; exact hwv2) hwv1
    obtain ⟨c₁, hc₁, e₁⟩ := outer_classes.1 w hw hw2
    obtain ⟨c₂, hc₂, e₂⟩ := outer_classes.1 (w * v) hw' ho'
    refine ⟨c₁ * c₂⁻¹, P.mul_mem hc₁ (P.inv_mem hc₂), ?_⟩
    calc (c₁ * c₂⁻¹)⁻¹ * w * (c₁ * c₂⁻¹) = c₂ * (c₁⁻¹ * w * c₁) * c₂⁻¹ := by group
      _ = c₂ * permU * c₂⁻¹ := by rw [e₁]; group
      _ = w * v := e₂.symm

end Model

section NoL34

variable {G : Type} [Group G]

theorem card_center_quot_dvd_range {Y : Subgroup G} {Q : Type*} [Group Q] (ψ : ↥Y →* Q)
    (hψ : ψ.ker ≤ Subgroup.center ↥Y) :
    Nat.card (↥Y ⧸ Subgroup.center ↥Y) ∣ Nat.card ψ.range := by
  have h := Subgroup.index_dvd_of_le hψ
  rw [Subgroup.index_ker] at h
  exact h

theorem j2NoL34Component :
    J2NoL34Component := by
  intro G _ _ X Y i hXq _ ⟨e⟩ hi hi2 hcomm hY hL34
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* J2Cover.P :=
    (e : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.J2).trans J2Cover.nativeEquivP
  have hπ := quotProj_surjective e'
  have hker := quotProj_ker e'
  have hYX : Y ≤ X := hY.1.trans inf_le_left
  have hYi : Y ≤ Subgroup.centralizer ({i} : Set G) := hY.1.trans inf_le_right
  have hα2 := quotAct_mul_self (quotProj e') hπ hker hi hi2
  have hα1 := quotAct_ne_one (quotProj e') hπ hker hi hXq hcomm
  let ψ : ↥Y →* J2Cover.P := (quotProj e').comp (Subgroup.inclusion hYX)
  have hψfix : ψ.range ≤ fixSub (quotAct (quotProj e') hπ hker hi) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_fixSub]
    have hy : ((Subgroup.inclusion hYX y : X) : G) = i * (Subgroup.inclusion hYX y : X) * i⁻¹ := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hYi y.2)
      rw [Subgroup.coe_inclusion]
      calc (y : G) = (y * i) * i⁻¹ := by group
        _ = (i * y) * i⁻¹ := by rw [this]
    exact quotAct_apply (quotProj e') hπ hker hi _ _ hy
  have hker_le : ψ.ker ≤ Subgroup.center ↥Y := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have hz : Subgroup.inclusion hYX y ∈ Subgroup.center ↥X := by
      rw [← hker]
      exact MonoidHom.mem_ker.mpr hy
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y'
    apply Subtype.ext
    exact congrArg (Subtype.val : ↥X → G) (hz (Subgroup.inclusion hYX y'))
  have hdvd1 := card_center_quot_dvd_range ψ hker_le
  have h20160 : Nat.card (↥Y ⧸ Subgroup.center ↥Y) = 20160 := card_of_psl_three_four hL34
  have hdvd2 : Nat.card ψ.range ∣ Nat.card (fixSub (quotAct (quotProj e') hπ hker hi)) :=
    Subgroup.card_dvd_of_le hψfix
  have hdvd : 20160 ∣ Nat.card (fixSub (quotAct (quotProj e') hπ hker hi)) := by
    rw [← h20160]
    exact hdvd1.trans hdvd2
  rcases j2_fixSub_card _ hα2 hα1 with h | h | h <;> rw [h] at hdvd <;> omega

end NoL34

section Conj

theorem tabConj_patB
    (G : Type) [Group G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (ht : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hK : K = CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf
      (X ⊓ Subgroup.centralizer ({t} : Set G)))
    (hpat : PatB X K t) (hZ : Subgroup.center ↥X = ⊥) :
    ∀ u ∈ K, u * u = 1 → ∃ x ∈ X, x⁻¹ * t * x = t * u := by
  intro u huK hu2
  obtain ⟨-, ⟨e⟩, -, hout⟩ := hpat
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* J2Cover.P :=
    (e : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.J2).trans J2Cover.nativeEquivP
  have hπ := quotProj_surjective e'
  have hker := quotProj_ker e'
  have hX : Group.IsPerfect ↥X := hXq.1
  set π := quotProj e' with hπdef
  set α := quotAct π hπ hker ht with hαdef
  have hα2 : α * α = 1 := quotAct_mul_self π hπ hker ht ht2
  have hαout : α ∉ inner J2Cover.P := fun h =>
    hout (inducesInner_of_quotAct_mem_inner π hπ hker ht hX ht2 h)
  obtain ⟨w, hw, hw2, hαw⟩ := j2_outer_conj α hα2 hαout
  have hww : w * w = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one w
    rwa [hw2] at this
  have hKXt : K ≤ X ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [hK]
    exact perfectResidualOf_le _
  have huX : u ∈ X := (hKXt huK).1
  have hut : u * t = t * u := Subgroup.mem_centralizer_singleton_iff.mp (hKXt huK).2
  obtain ⟨uX, huXeq⟩ : ∃ uX : X, (uX : G) = u := ⟨⟨u, huX⟩, rfl⟩
  have hfix : α (π uX) = π uX := by
    refine quotAct_apply π hπ hker ht uX uX ?_
    rw [huXeq]
    calc u = (u * t) * t⁻¹ := by group
      _ = (t * u) * t⁻¹ := by rw [hut]
  have hvw : ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) * w =
      w * ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) := by
    have h1 := hαw (π uX)
    rw [hfix] at h1
    calc ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) * w
        = (w * ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) * w⁻¹) * w := by rw [← h1]
      _ = w * ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) := by group
  have hv2 : ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) *
      ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) = 1 := by
    have hsq : π uX * π uX = 1 := by
      rw [← map_mul]
      have : uX * uX = 1 := Subtype.ext (by rw [Subgroup.coe_mul, huXeq, hu2]; rfl)
      rw [this, map_one]
    simpa using congrArg Subtype.val hsq
  obtain ⟨xb, hxb, hxbw⟩ := j2_outer_fusion hw hw2 (π uX).2 hvw hv2
  obtain ⟨x₀, hx₀⟩ := hπ ⟨xb, hxb⟩
  obtain ⟨y, hy⟩ : ∃ y : X, (y : G) = t * x₀ * t⁻¹ := ⟨conjAut X t ht x₀, coe_conjAut X ht x₀⟩
  have hαx : α (π x₀) = π y := quotAct_apply π hπ hker ht x₀ y hy
  have hkey : π (y⁻¹ * x₀) = π uX := by
    apply Subtype.ext
    have h1 : ((α (π x₀) : J2Cover.P) : Equiv.Perm (Fin 315)) = w * xb * w⁻¹ := by
      rw [hαw, hx₀]
    have h2 : ((π y : J2Cover.P) : Equiv.Perm (Fin 315)) = w * xb * w⁻¹ := by
      rw [← hαx, h1]
    rw [map_mul, map_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2, hx₀]
    have hwi : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
    rw [hwi]
    calc (w * xb * w)⁻¹ * xb = w⁻¹ * xb⁻¹ * w⁻¹ * xb := by group
      _ = w * xb⁻¹ * w * xb := by rw [hwi]
      _ = w * (xb⁻¹ * w * xb) := by group
      _ = w * (w * ((π uX : J2Cover.P) : Equiv.Perm (Fin 315))) := by rw [hxbw]
      _ = ((π uX : J2Cover.P) : Equiv.Perm (Fin 315)) := by rw [← mul_assoc, hww, one_mul]
  have hmem : (y⁻¹ * x₀) * uX⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkey, mul_inv_cancel]
  rw [hker, hZ, Subgroup.mem_bot] at hmem
  have heq : y⁻¹ * x₀ = uX := mul_inv_eq_one.mp hmem
  refine ⟨(x₀ : G), x₀.2, ?_⟩
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have h3 : (t * (x₀ : G) * t⁻¹)⁻¹ * x₀ = u := by
    have := congrArg Subtype.val heq
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hy, huXeq] at this
    exact this
  have h4 : (x₀ : G)⁻¹ * t⁻¹ * x₀ = t⁻¹ * u := by
    calc (x₀ : G)⁻¹ * t⁻¹ * x₀ = t⁻¹ * ((t * (x₀ : G) * t⁻¹)⁻¹ * x₀) := by group
      _ = t⁻¹ * u := by rw [h3]
  rw [hinv] at h4
  exact h4

end Conj

section Cover

theorem tabJ2Cover_of_isPGroup
    (G : Type) [Group G] [Finite G] (X K : Subgroup G) (t : G)
    (hXq : CFSG.IsQuasisimple ↥X) (htN : t ∈ Subgroup.normalizer (X : Set G)) (ht2 : t * t = 1)
    (hpat : PatB X K t) (hZ2 : IsPGroup 2 (Subgroup.center ↥X)) :
    ∀ i ∈ centerOf X, i ≠ 1 → ∃ x ∈ X, x⁻¹ * t * x = t * i := by
  intro i hi hi1
  obtain ⟨-, ⟨e⟩, -, hout⟩ := hpat
  have hi' : i ∈ X ⊓ Subgroup.centralizer (X : Set G) := hi
  have hiX : i ∈ X := hi'.1
  have hic : ∀ x ∈ X, x * i = i * x := Subgroup.mem_centralizer_iff.mp hi'.2
  let e' : (↥X ⧸ Subgroup.center ↥X) ≃* J2Cover.P :=
    (e : (↥X ⧸ Subgroup.center ↥X) ≃* NativeSporadic.J2).trans J2Cover.nativeEquivP
  have hXq' : CFSG.Assembly.IsQuasisimple ↥X := ⟨Group.isPerfect_def.1 hXq.1, hXq.2.1⟩
  have hcard : Nat.card (Subgroup.center ↥X) ≤ 2 :=
    StandardRecognition.m12J2CentralTwoGroupOrderBound ↥X hXq' hZ2 (Or.inr ⟨e⟩)
  have hX : Group.IsPerfect ↥X := hXq.1
  set H : Subgroup G := X ⊔ Subgroup.zpowers t with hHdef
  have hXH : X ≤ H := le_sup_left
  have htH : t ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hiH : i ∈ H := hXH hiX
  have hHnorm : H ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 htN)
  have hLnorm : (X.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).2 hHnorm
  let eL : ↥(X.subgroupOf H) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXH
  let i' : ↥X := ⟨i, hiX⟩
  have hi'c : i' ∈ Subgroup.center ↥X :=
    Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hic x.1 x.2)
  have hi'1 : i' ≠ 1 := fun h => hi1 (congrArg Subtype.val h)
  have hi'2 : orderOf i' = 2 := by
    have hd : orderOf i' ∣ Nat.card (Subgroup.center ↥X) :=
      Subgroup.orderOf_dvd_natCard (Subgroup.center ↥X) hi'c
    have hpos : 0 < Nat.card (Subgroup.center ↥X) := Nat.card_pos
    have h1 := Nat.le_of_dvd hpos hd
    have h2 : orderOf i' ≠ 1 := fun h => hi'1 (orderOf_eq_one_iff.mp h)
    have h3 : 0 < orderOf i' := orderOf_pos i'
    omega
  have hi'sq : i' * i' = 1 := by
    rw [← sq]
    have := pow_orderOf_eq_one i'
    rwa [hi'2] at this
  have hZeq : Subgroup.center ↥X = Subgroup.zpowers i' := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hi'c)
    rw [Nat.card_zpowers, hi'2]
    exact hcard
  have hic' : i ∈ Subgroup.centralizer (X : Set G) := Subgroup.mem_centralizer_iff.mpr hic
  have hti : t * i = i * t := by
    have hc := conj_mem_center htN (show i ∈ X ⊓ Subgroup.centralizer (X : Set G) from ⟨hiX, hic'⟩)
    have hz : (⟨t * i * t⁻¹, hc.1⟩ : ↥X) ∈ Subgroup.center ↥X :=
      Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hc.2 g g.2)
    rw [hZeq] at hz
    rcases mem_zpowers_involution hi'sq hz with h | h
    · exact absurd (by
        have := congrArg Subtype.val h
        simpa using this) hi1
    · have := congrArg Subtype.val h
      simp only at this
      calc t * i = t * i * t⁻¹ * t := by group
        _ = i * t := by rw [this]
  let t' : ↥(X.subgroupOf H) := ⟨⟨i, hiH⟩, Subgroup.mem_subgroupOf.2 hiX⟩
  have hteL : eL t' = i' := rfl
  have ht'2 : orderOf t' = 2 := by rw [← hi'2, ← hteL, MulEquiv.orderOf_eq]
  have hZL : Subgroup.center ↥(X.subgroupOf H) = Subgroup.zpowers t' := by
    ext l
    constructor
    · intro hl
      have h1 : eL l ∈ Subgroup.zpowers i' := hZeq ▸ (mem_center_iff_equiv eL l).2 hl
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h1
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, eL.injective ?_⟩
      rw [map_zpow, hteL, hn]
    · intro hl
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hl
      rw [← mem_center_iff_equiv eL, map_zpow, hteL, hZeq]
      exact Subgroup.zpow_mem_zpowers i' n
  let π : ↥(X.subgroupOf H) →* J2Cover.P := (quotProj e').comp eL.toMonoidHom
  have hπ : Function.Surjective π := (quotProj_surjective e').comp eL.surjective
  have hker : π.ker = Subgroup.zpowers t' := by
    ext l
    rw [← hZL, ← mem_center_iff_equiv eL, ← quotProj_ker e']
    exact Iff.rfl
  have hLq : CFSG.Assembly.IsQuasisimple ↥(X.subgroupOf H) := by
    have : Group.IsPerfect ↥(X.subgroupOf H) :=
      Group.IsPerfect.ofSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
    refine ⟨Group.isPerfect_def.1 this, ?_⟩
    have e2 : (↥(X.subgroupOf H) ⧸ Subgroup.center ↥(X.subgroupOf H)) ≃*
        (↥X ⧸ Subgroup.center ↥X) :=
      QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)
    have : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hXq.2.1
    exact e2.isSimpleGroup
  have hCL : Subgroup.centralizer ((X.subgroupOf H : Subgroup ↥H) : Set ↥H) =
      Subgroup.zpowers ((t' : ↥(X.subgroupOf H)) : ↥H) := by
    apply le_antisymm
    · intro h hh
      rw [Subgroup.mem_centralizer_iff] at hh
      have hmem := (CFSG.Sporadic.SmallOddCore.mem_sup_zpowers_iff (P := X) (u := t)
        (by rw [sq]; exact ht2)
        (fun p hp => (Subgroup.mem_normalizer_iff.mp htN p).mp hp)).mp h.2
      rcases hmem with hgX | hgtX
      · have hl : h ∈ X.subgroupOf H := Subgroup.mem_subgroupOf.2 hgX
        have hlc : (⟨h, hl⟩ : ↥(X.subgroupOf H)) ∈ Subgroup.center ↥(X.subgroupOf H) :=
          Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hh m.1 m.2)
        rw [hZL] at hlc
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hlc
        refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
        have := congrArg Subtype.val hn
        simpa using this
      · exfalso
        apply hout
        refine ⟨(h : G) * t, hgtX, fun y hy => ?_⟩
        have hy' : (y : G) * (h : G) = (h : G) * y :=
          congrArg Subtype.val (hh ⟨y, hXH hy⟩ (Subgroup.mem_subgroupOf.2 hy))
        have hcc : (h : G)⁻¹ * y * (h : G) = y := by
          rw [mul_assoc, hy', ← mul_assoc, inv_mul_cancel, one_mul]
        calc t⁻¹ * y * t = t⁻¹ * ((h : G)⁻¹ * y * (h : G)) * t := by rw [hcc]
          _ = ((h : G) * t)⁻¹ * y * ((h : G) * t) := by group
    · intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have htc : t' ∈ Subgroup.center ↥(X.subgroupOf H) := hZL ▸ Subgroup.mem_zpowers t'
      have hc : Commute m ((t' : ↥(X.subgroupOf H)) : ↥H) :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp htc ⟨m, hm⟩)
      exact (hc.zpow_right n).eq
  let p : ↥H := ⟨t, htH⟩
  have hpL : p ∉ X.subgroupOf H := fun h =>
    hout (Ch1.InducesInner.of_mem (Subgroup.mem_subgroupOf.mp h))
  have ht1 : t ≠ 1 := fun h => hout (Ch1.InducesInner.of_mem (h ▸ X.one_mem))
  have hp2 : orderOf p = 2 := by
    rw [show orderOf p = orderOf t from Subgroup.orderOf_mk t htH]
    exact orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  have hkerC : π.ker = Subgroup.center ↥(X.subgroupOf H) := hker.trans hZL.symm
  have hα : ∀ l : ↥(X.subgroupOf H),
      CentralCover.fullAction π hπ hkerC p (π l) = π (MulAut.conjNormal p l) := fun l =>
    CentralCover.fullAction_apply π hπ hkerC p l
  have hfull := J2Cover.ctss_j2_actual_double_cover_external_conjugacy_and_exact_fixed_section
    (H := ↥H) (L := X.subgroupOf H) hLq ht'2 hZL π hπ hker hCL
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, c, hc, -, -, -, hv⟩ :=
    hfull.2 p hpL hp2 _ hα
  obtain ⟨v, hvc⟩ := hπ c
  have hv' := (hv v hvc).2.2.2.2
  have hvG := congrArg (fun h : ↥H => (h : G)) hv'
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hvG
  have hvX : (((v : ↥H)) : G) ∈ X := Subgroup.mem_subgroupOf.mp v.2
  refine ⟨(((v : ↥H)) : G)⁻¹, X.inv_mem hvX, ?_⟩
  rw [inv_inv]
  exact hvG.trans hti.symm

end Cover

end CFSG.QuasithinUnique.Id2519.Tab
