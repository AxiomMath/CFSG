module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldData
public import CFSG.GH74.GLS.C3.Layer1.Th2P412Cv
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Alt4G
public import CFSG.GH74.GLS.C3.Layer1.BkL114Mod11
public import CFSG.GH74.GLS.C3.Layer1.BkL114Mod9
public import CFSG.GH74.GLS.C3.Layer1.Th2AModelSucc
public import CFSG.GH74.GLS.C3.Layer1.Th2AltCv
public import CFSG.GH74.GLS.C3.Layer1.Th2AltCvA
public import CFSG.GH74.GLS.C3.Layer1.Th2AltFus
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltCv2
public import CFSG.GH74.GLS.C3.Layer1.Th2P85AltTIQ
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.GH74.GLS.Th2.AltCv

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.GH74.GLS.Th2.P85 CFSG.GH74.GLS.Th2.P85.Alt CFSG.GH74.GLS.C3.Layer2
  CFSG.GH74.GLS.C3.Layer1.Bk CFSG.GH74.GLS.Th2.P412

variable {G : Type} [Group G] [Finite G]

theorem centralizer_v_le_of_gold
    (hGold : GoldStmt) (hN11a : CFSG.Goldschmidt.S_N11a) (hN11b : CFSG.Goldschmidt.S_N11b)
    (M S : Subgroup G) (x v : G) (hxM : x ∈ M) (hvM : v ∈ M) (hSM : S ≤ M) (hxS : x ∈ S)
    (hSyl : IsSylowOf 2 S ⊤) (hx2 : orderOf x = 2) (hv2 : orderOf v = 2)
    (hvc : ∀ s ∈ S, s * v = v * s) (hnc : ¬ IsConj x v) (hF : ∀ g : G, g * x * g⁻¹ ∈ M → g ∈ M)
    (hS128 : Nat.card S ≤ 128) (hti : TIMOutQ M S x v hxM hvM) :
    centralizer ({v} : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨EM, hEMS, hxEM, hvEM, hEMcard, hEMcomm, hEMsq, hEMnorm, hEMiff, hEMtrans,
      ⟨s₁, hs₁S, hs₁sq, hs₁E⟩, hEMZ⟩ := hti
  have hxsq : x * x = 1 := by
    have h1 := pow_orderOf_eq_one x
    rw [hx2, sq] at h1
    exact h1
  have hvsq : v * v = 1 := by
    have h1 := pow_orderOf_eq_one v
    rw [hv2, sq] at h1
    exact h1
  have hx1 : x ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx2
    omega
  have hv1 : v ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hv2
    omega
  have hCM : ∀ g : G, g * x = x * g → g ∈ M := by
    intro g hg
    refine hF g ?_
    have h1 : g * x * g⁻¹ = x := by rw [hg]; group
    rw [h1]
    exact hxM
  have hxvE : (⟨x, hxM⟩ : ↥M) * ⟨v, hvM⟩ ∈ EM := EM.mul_mem hxEM hvEM
  have hxv1 : (⟨x, hxM⟩ : ↥M) * ⟨v, hvM⟩ ≠ 1 := by
    intro h1
    apply hnc
    have h2 : x * v = 1 := congrArg Subtype.val h1
    have h3 : x = v := by
      calc x = x * (v * v) := by rw [hvsq, mul_one]
        _ = (x * v) * v := by rw [mul_assoc]
        _ = v := by rw [h2, one_mul]
    rw [h3]
  have hxvv : (⟨x, hxM⟩ : ↥M) * ⟨v, hvM⟩ ≠ ⟨v, hvM⟩ := by
    intro h1
    have h2 : x * v = v := congrArg Subtype.val h1
    exact hx1 (mul_right_cancel (h2.trans (one_mul v).symm))
  obtain ⟨c₀, hc₀v, hc₀x⟩ := hEMtrans _ hxvE hxv1 hxvv
  have hxxv : x * v = (c₀ : G) * x * (c₀ : G)⁻¹ := (congrArg Subtype.val hc₀x).symm
  set Cv : Subgroup G := centralizer ({v} : Set G) with hCv
  have hmemCv : ∀ g : G, g ∈ Cv ↔ g * v = v * g := fun g => mem_centralizer_singleton_iff
  have hSCv : S ≤ Cv := fun s hs => (hmemCv s).2 (hvc s hs)
  have hxCv : x ∈ Cv := hSCv hxS
  have hc₀Cv : (c₀ : G) ∈ Cv := (hmemCv _).2 (congrArg Subtype.val hc₀v)
  let EG : Subgroup G := EM.map M.subtype
  have hmemEG : ∀ y : G, y ∈ EG ↔ ∃ hyM : y ∈ M, (⟨y, hyM⟩ : ↥M) ∈ EM := by
    intro y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨m.2, hm⟩
    · rintro ⟨hyM, hm⟩
      exact ⟨⟨y, hyM⟩, hm, rfl⟩
  have hEGS : EG ≤ S := by
    rintro _ ⟨m, hm, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hEMS hm)
  have hEGCv : EG ≤ Cv := hEGS.trans hSCv
  have hEGcard : Nat.card EG = 8 := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact hEMcard
  have hxEG : x ∈ EG := (hmemEG x).2 ⟨hxM, hxEM⟩
  have hvEG : v ∈ EG := (hmemEG v).2 ⟨hvM, hvEM⟩
  have hxvconj : ∀ g ∈ Cv, (g * x * g⁻¹) * v = (g * c₀) * x * (g * c₀)⁻¹ := by
    intro g hg
    have hgv : g * v = v * g := (hmemCv g).1 hg
    have hgv' : g⁻¹ * v = v * g⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul]
      calc v = (v * g) * g⁻¹ := by group
        _ = (g * v) * g⁻¹ := by rw [hgv]
        _ = g * (v * g⁻¹) := by group
    calc (g * x * g⁻¹) * v = g * x * (g⁻¹ * v) := by group
      _ = g * x * (v * g⁻¹) := by rw [hgv']
      _ = g * (x * v) * g⁻¹ := by group
      _ = g * ((c₀ : G) * x * (c₀ : G)⁻¹) * g⁻¹ := by rw [hxxv]
      _ = (g * c₀) * x * (g * c₀)⁻¹ := by group
  let Zs : Set G := {z | ∃ g ∈ Cv, g * x * g⁻¹ = z}
  have hFvE : ∀ y ∈ S, y ∈ Fv x v ↔ (y ∈ EG ∧ y ≠ 1 ∧ y ≠ v) := by
    intro y hyS
    have hyM : y ∈ M := hSM hyS
    let yM : ↥M := ⟨y, hyM⟩
    have hyMS : yM ∈ S.subgroupOf M := hyS
    constructor
    · rintro ⟨hyc, hy2, hxy, hxyv⟩
      obtain ⟨g, hg⟩ := isConj_iff.1 hxy
      obtain ⟨g', hg'⟩ := isConj_iff.1 hxyv
      have hgM : g ∈ M := hF g (by rw [hg]; exact hyM)
      have hg'M : g' ∈ M := hF g' (by rw [hg']; exact M.mul_mem hyM hvM)
      have hy1 : y ≠ 1 := by
        intro h1
        apply hx1
        rw [← hg] at h1
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [h1]; group
      obtain ⟨hyE, -, hyv⟩ := (hEMiff yM hyMS).1 ⟨Subtype.ext hy2, fun h => hy1 (congrArg Subtype.val h),
        Subtype.ext hyc, isConj_iff.2 ⟨⟨g, hgM⟩, Subtype.ext hg⟩,
        isConj_iff.2 ⟨⟨g', hg'M⟩, Subtype.ext hg'⟩⟩
      exact ⟨(hmemEG y).2 ⟨hyM, hyE⟩, hy1, fun h => hyv (Subtype.ext h)⟩
    · rintro ⟨hyE, hy1, hyv⟩
      obtain ⟨_, hyEM⟩ := (hmemEG y).1 hyE
      obtain ⟨c, hcv, hcx⟩ := hEMtrans yM hyEM (fun h => hy1 (congrArg Subtype.val h))
        (fun h => hyv (congrArg Subtype.val h))
      have hcCv : (c : G) ∈ Cv := (hmemCv _).2 (congrArg Subtype.val hcv)
      have hcxG : (c : G) * x * (c : G)⁻¹ = y := congrArg Subtype.val hcx
      refine ⟨(hvc y hyS), ?_, isConj_iff.2 ⟨c, hcxG⟩, ?_⟩
      · rw [← hcxG]
        calc (c : G) * x * (c : G)⁻¹ * ((c : G) * x * (c : G)⁻¹)
            = (c : G) * (x * x) * (c : G)⁻¹ := by group
          _ = 1 := by rw [hxsq]; group
      · rw [← hcxG, hxvconj (c : G) hcCv]
        exact isConj_iff.2 ⟨(c : G) * (c₀ : G), rfl⟩
  have hEv : Ev x v S = EG := by
    unfold Ev
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro t (ht | ⟨htF, htS⟩)
      · rw [Set.mem_singleton_iff.1 ht]; exact hvEG
      · exact ((hFvE t htS).1 htF).1
    · intro y hy
      by_cases hy1 : y = 1
      · rw [hy1]; exact one_mem _
      by_cases hyv : y = v
      · rw [hyv]; exact Subgroup.subset_closure (Or.inl rfl)
      exact Subgroup.subset_closure (Or.inr ⟨(hFvE y (hEGS hy)).2 ⟨hy, hy1, hyv⟩, hEGS hy⟩)
  have hvCv : v ∈ Cv := (hmemCv v).2 rfl
  have hv_comm : ∀ c ∈ Cv, c * v = v * c := fun c hc => (hmemCv c).1 hc
  have hZ_sq : ∀ z ∈ Zs, z * z = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
      _ = 1 := by rw [hxsq]; group
  have hZ_ne : ∀ z ∈ Zs, z ≠ 1 := by
    rintro _ ⟨g, hg, rfl⟩ h1
    apply hx1
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  have hv_nmem : v ∉ Zs := by
    rintro ⟨g, hg, hgv⟩
    exact hnc (isConj_iff.2 ⟨g, hgv⟩)
  have hZC_conj : ∀ z ∈ Zs, ∀ g ∈ Cv, g * z * g⁻¹ ∈ Zs := by
    rintro _ ⟨h, hh, rfl⟩ g hg
    exact ⟨g * h, Cv.mul_mem hg hh, by group⟩
  have hZmv : ∀ z ∈ Zs, z * v ∈ Zs := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g * c₀, Cv.mul_mem hg hc₀Cv, (hxvconj g hg).symm⟩
  have hE_comm : ∀ a ∈ EG, ∀ b ∈ EG, a * b = b * a := by
    intro a ha b hb
    obtain ⟨haM, haE⟩ := (hmemEG a).1 ha
    obtain ⟨hbM, hbE⟩ := (hmemEG b).1 hb
    exact congrArg Subtype.val (hEMcomm _ haE _ hbE)
  have hE_sq : ∀ a ∈ EG, a * a = 1 := by
    intro a ha
    obtain ⟨haM, haE⟩ := (hmemEG a).1 ha
    exact congrArg Subtype.val (hEMsq _ haE)
  have hS_norm : ∀ s ∈ S, ∀ y ∈ EG, s * y * s⁻¹ ∈ EG := by
    intro s hs y hy
    obtain ⟨hy1, hy2⟩ := (hmemEG y).1 hy
    have hsM : s ∈ M := hSM hs
    have := hEMnorm ⟨s, hsM⟩ hs _ hy2
    exact (hmemEG _).2 ⟨M.mul_mem (M.mul_mem hsM hy1) (M.inv_mem hsM), this⟩
  have hZ_inter : ∀ y ∈ S, y ∈ Zs ↔ (y ∈ EG ∧ y ≠ 1 ∧ y ≠ v) := by
    intro y hyS
    rw [← hFvE y hyS]
    constructor
    · rintro ⟨g, hg, hgy⟩
      refine ⟨hvc y hyS, ?_, isConj_iff.2 ⟨g, hgy⟩, ?_⟩
      · rw [← hgy]
        calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
          _ = 1 := by rw [hxsq]; group
      · rw [← hgy, hxvconj g hg]
        exact isConj_iff.2 ⟨g * (c₀ : G), rfl⟩
    · intro hyF
      obtain ⟨hyE, hy1, hyv⟩ := (hFvE y hyS).1 hyF
      obtain ⟨hyM, hyEM⟩ := (hmemEG y).1 hyE
      obtain ⟨c, hcv, hcx⟩ := hEMtrans ⟨y, hyM⟩ hyEM (fun h => hy1 (congrArg Subtype.val h))
        (fun h => hyv (congrArg Subtype.val h))
      exact ⟨(c : G), (hmemCv _).2 (congrArg Subtype.val hcv), congrArg Subtype.val hcx⟩
  have hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ EG :=
    ⟨(s₁ : G), Subgroup.mem_subgroupOf.1 hs₁S, congrArg Subtype.val hs₁sq, fun hmem => hs₁E (by
      obtain ⟨_, hm⟩ := (hmemEG _).1 hmem
      exact hm)⟩
  have hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v := by
    intro s hs hsc hsq hs1
    have hsM : s ∈ M := hSM hs
    have := hEMZ ⟨s, hsM⟩ hs (fun t ht => Subtype.ext (hsc t.1 (Subgroup.mem_subgroupOf.1 ht)))
      (Subtype.ext hsq) (fun h1 => hs1 (congrArg Subtype.val h1))
    exact congrArg Subtype.val this
  have hNO : ∀ g ∈ Cv, ∀ e ∈ EG,
      ∃ e' ∈ EG, ∃ o ∈ pPrimeCoreOf 2 Cv, g * e * g⁻¹ = e' * o := fun g hg e he =>
    gold_cent_of_data hGold hN11a hN11b hvCv hxCv hSCv hvsq hv1 hv_comm hZ_sq hZ_ne hv_nmem
      hZC_conj hZmv (hSyl.of_le hSCv le_top) hEGS hEGcard hE_comm hE_sq hvEG hS_norm hZ_inter
      ⟨1, one_mem _, by simp⟩ hxEG (fun z hz => hz) hS128 hex g hg e he
  have hC_of_E : ∀ a ∈ EG, a ≠ 1 → a ≠ v → centralizer ({a} : Set G) ≤ M := by
    intro a haE ha1 hav g hg
    obtain ⟨haM, haEM⟩ := (hmemEG a).1 haE
    obtain ⟨c, hcv, hcx⟩ := hEMtrans ⟨a, haM⟩ haEM (fun h => ha1 (congrArg Subtype.val h))
      (fun h => hav (congrArg Subtype.val h))
    have hcxG : (c : G) * x * (c : G)⁻¹ = a := congrArg Subtype.val hcx
    have hga : g * a = a * g := mem_centralizer_singleton_iff.1 hg
    have hmem : (c : G)⁻¹ * g * (c : G) ∈ M := by
      apply hCM
      calc (c : G)⁻¹ * g * (c : G) * x = (c : G)⁻¹ * (g * ((c : G) * x * (c : G)⁻¹)) * (c : G) := by
            group
        _ = (c : G)⁻¹ * (g * a) * (c : G) := by rw [hcxG]
        _ = (c : G)⁻¹ * (a * g) * (c : G) := by rw [hga]
        _ = (c : G)⁻¹ * (((c : G) * x * (c : G)⁻¹) * g) * (c : G) := by rw [hcxG]
        _ = x * ((c : G)⁻¹ * g * (c : G)) := by group
    have : g = (c : G) * ((c : G)⁻¹ * g * (c : G)) * (c : G)⁻¹ := by group
    rw [this]
    exact M.mul_mem (M.mul_mem c.2 hmem) (M.inv_mem c.2)
  have hOM : pPrimeCoreOf 2 Cv ≤ M := by
    have hx2' : x ^ 2 = 1 := by rw [sq]; exact hxsq
    have hv2' : v ^ 2 = 1 := by rw [sq]; exact hvsq
    have hxvne : x ≠ v := fun h => hnc (h ▸ IsConj.refl x)
    have hxvc : x * v = v * x := hvc x hxS
    have hA0card : Nat.card ↥(zpowers x ⊔ zpowers v) = 4 :=
      C3.Layer1.P89.card_klein hx2' hv2' hxvc hx1 hv1 hxvne
    obtain ⟨y₁, hy₁E, hy₁A⟩ : ∃ y₁ ∈ EG, y₁ ∉ zpowers x ⊔ zpowers v := by
      by_contra hcon
      push Not at hcon
      have hle : EG ≤ zpowers x ⊔ zpowers v := fun y hy => hcon y hy
      have := Subgroup.card_le_of_le hle
      rw [hEGcard, hA0card] at this
      omega
    have hy₁sq : y₁ * y₁ = 1 := hE_sq y₁ hy₁E
    have hy₁2' : y₁ ^ 2 = 1 := by rw [sq]; exact hy₁sq
    have hy₁1 : y₁ ≠ 1 := fun h => hy₁A (by rw [h]; exact one_mem _)
    have hy₁x : y₁ ≠ x := fun h => hy₁A (by rw [h]; exact Subgroup.mem_sup_left (mem_zpowers x))
    have hy₁v : y₁ ≠ v := fun h => hy₁A (by rw [h]; exact Subgroup.mem_sup_right (mem_zpowers v))
    have hxy₁ : x * y₁ = y₁ * x := hE_comm x hxEG y₁ hy₁E
    have hA := C3.Layer1.P89.isElemAbelian_pair hx2' hy₁2' hxy₁
    have hAcard := C3.Layer1.P89.card_klein hx2' hy₁2' hxy₁ hx1 hy₁1 hy₁x.symm
    have hcomm : ∀ a ∈ zpowers x, ∀ b ∈ zpowers y₁, a * b = b * a := by
      intro a ha b hb
      rcases C3.Layer1.P89.mem_zpowers_of_sq hx2' ha with h1 | h1 <;>
        rcases C3.Layer1.P89.mem_zpowers_of_sq hy₁2' hb with h2 | h2 <;> simp [h1, h2, hxy₁]
    have hCa : ∀ a ∈ zpowers x ⊔ zpowers y₁, a ≠ 1 → centralizer ({a} : Set G) ≤ M := by
      intro a ha ha1
      obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := Uniqueness.SU.SU1.mem_sup_of_commute hcomm ha
      have hmemE : a₁ * b₁ ∈ EG :=
        EG.mul_mem ((zpowers_le.2 hxEG) ha₁) ((zpowers_le.2 hy₁E) hb₁)
      have hav : a₁ * b₁ ≠ v := by
        intro hav
        rcases C3.Layer1.P89.mem_zpowers_of_sq hx2' ha₁ with h1 | h1 <;>
          rcases C3.Layer1.P89.mem_zpowers_of_sq hy₁2' hb₁ with h2 | h2
        · exact ha1 (by rw [h1, h2, one_mul])
        · rw [h1, h2, one_mul] at hav
          exact hy₁v hav
        · rw [h1, h2, mul_one] at hav
          exact hxvne hav
        · rw [h1, h2] at hav
          apply hy₁A
          have : y₁ = x * v := by
            calc y₁ = (x * x) * y₁ := by rw [hxsq, one_mul]
              _ = x * (x * y₁) := by rw [mul_assoc]
              _ = x * v := by rw [hav]
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers x))
            (Subgroup.mem_sup_right (mem_zpowers v))
      exact hC_of_E _ hmemE ha1 hav
    have hAC : zpowers x ⊔ zpowers y₁ ≤ Cv :=
      sup_le (zpowers_le.2 (hEGCv hxEG)) (zpowers_le.2 (hEGCv hy₁E))
    have hAN : zpowers x ⊔ zpowers y₁ ≤ normalizer (pPrimeCoreOf 2 Cv : Set G) := by
      intro a ha
      have haCv := hAC ha
      rw [mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        exact TwoThin.pPrimeCoreOf_normalized Cv haCv hn
      · intro hn
        have h := TwoThin.pPrimeCoreOf_normalized Cv (Cv.inv_mem haCv) hn
        rwa [show a⁻¹ * (a * n * a⁻¹) * a⁻¹⁻¹ = n by group] at h
    have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity (p := 2)
      Nat.prime_two hA (by rw [hAcard]; norm_num) hAN
      (Nat.coprime_two_left.2 (TwoThin.card_pPrimeCoreOf_odd Cv))
    have hle : (⨆ (a : G) (_ : a ∈ zpowers x ⊔ zpowers y₁) (_ : a ≠ 1),
        pPrimeCoreOf 2 Cv ⊓ centralizer ({a} : Set G)) ≤ M := by
      refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
      exact inf_le_right.trans (hCa a ha ha1)
    rw [hgen] at hle
    exact hle
  let E' : Subgroup ↥Cv := EG.subgroupOf Cv
  let O' : Subgroup ↥Cv := pPrimeCore 2 ↥Cv
  have hO'normal : O'.Normal := pPrimeCore_normal
  have hE2 : IsPGroup 2 E' := (hSyl.isPGroup.to_le hEGS).comap_subtype
  have hN'normal : (O' ⊔ E').Normal := by
    letI : O'.Normal := hO'normal
    refine ⟨fun z hz g => ?_⟩
    obtain ⟨o, ho, e, he, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hz
    have hgo : g * o * g⁻¹ ∈ O' := hO'normal.conj_mem o ho g
    have hge : g * e * g⁻¹ ∈ O' ⊔ E' := by
      obtain ⟨e', he', o', ho', hEq⟩ := hNO (g : G) g.2 (e : G) (Subgroup.mem_subgroupOf.1 he)
      obtain ⟨o'', ho'', rfl⟩ := Subgroup.mem_map.1 ho'
      have he'C : (⟨e', (hEGS.trans hSCv) he'⟩ : ↥Cv) ∈ E' := by
        simpa [E'] using (Subgroup.mem_subgroupOf.2 he')
      have hEq' : g * e * g⁻¹ = (⟨e', (hEGS.trans hSCv) he'⟩ : ↥Cv) * o'' := by
        apply Subtype.ext
        simpa using hEq
      rw [hEq']
      exact (O' ⊔ E').mul_mem (Subgroup.mem_sup_right he'C) (Subgroup.mem_sup_left ho'')
    have hmain : g * (o * e) * g⁻¹ = (g * o * g⁻¹) * (g * e * g⁻¹) := by group
    rw [hmain]
    exact (O' ⊔ E').mul_mem (Subgroup.mem_sup_left hgo) hge
  have hfrattini : O' ⊔ normalizer (E' : Set ↥Cv) = ⊤ :=
    pPrimeCore_sup_normalizer_eq_top (p := 2) hE2 hN'normal
  intro c hc
  have hc_mem : (⟨c, hc⟩ : ↥Cv) ∈ O' ⊔ normalizer (E' : Set ↥Cv) := by
    rw [hfrattini]
    exact Subgroup.mem_top _
  letI : O'.Normal := hO'normal
  obtain ⟨o, ho, n, hn, hcon⟩ := Subgroup.mem_sup_of_normal_left.1 hc_mem
  have hoM : (o : G) ∈ M := hOM (Subgroup.mem_map.2 ⟨o, ho, rfl⟩)
  have hnNormG : (n : G) ∈ normalizer (EG : Set G) := by
    have hninv : n⁻¹ ∈ normalizer (E' : Set ↥Cv) := (normalizer (E' : Set ↥Cv)).inv_mem hn
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hy' : (⟨y, (hEGS.trans hSCv) hy⟩ : ↥Cv) ∈ E' := by
        simpa [E'] using (Subgroup.mem_subgroupOf.2 hy)
      have hconj : n * (⟨y, (hEGS.trans hSCv) hy⟩ : ↥Cv) * n⁻¹ ∈ E' :=
        (Subgroup.mem_normalizer_iff.1 hn _).1 hy'
      exact Subgroup.mem_subgroupOf.1 hconj
    · intro hy
      have hyCv : y ∈ Cv := by
        have hyEG : (n : G) * y * (n : G)⁻¹ ∈ EG := hy
        have : y = (n : G)⁻¹ * ((n : G) * y * (n : G)⁻¹) * (n : G) := by group
        rw [this]
        exact Cv.mul_mem (Cv.mul_mem (Cv.inv_mem n.2) ((hEGS.trans hSCv) hyEG)) n.2
      have hz' : (⟨(n : G) * y * (n : G)⁻¹, (hEGS.trans hSCv) hy⟩ : ↥Cv) ∈ E' := by
        simpa [E'] using (Subgroup.mem_subgroupOf.2 hy)
      have hconj : n⁻¹ * (⟨(n : G) * y * (n : G)⁻¹, (hEGS.trans hSCv) hy⟩ : ↥Cv) *
          (n⁻¹)⁻¹ ∈ E' :=
        (Subgroup.mem_normalizer_iff.1 hninv _).1 hz'
      have hy' : (⟨y, hyCv⟩ : ↥Cv) ∈ E' := by
        convert hconj using 1
        apply Subtype.ext
        simp [mul_assoc]
      exact Subgroup.mem_subgroupOf.1 hy'
  have hnM : (n : G) ∈ M :=
    hF (n : G) (hEGS.trans hSM ((Subgroup.mem_normalizer_iff.1 hnNormG x).1 hxEG))
  have hcEq : c = (o : G) * (n : G) := by
    have := congrArg Subtype.val hcon
    simpa using this.symm
  rw [hcEq]
  exact M.mul_mem hoM hnM

theorem alt_cv_of_gold
    (hGold : GoldStmt) (hN11a : CFSG.Goldschmidt.S_N11a)
    (hN11b : CFSG.Goldschmidt.S_N11b) {x y : G} {K T S M L : Subgroup G}
    (hstd : Th2Std x y K T S) (hKM : K ≤ M) (hxM : x ∈ M)
    (halt : Ivk73Alt (imgM M K) (imgM M L))
    (hCx : centralizer ({x} : Set G) ≤ M) :
    ∀ W : Subgroup G, IsSylowOf 2 W M → T ⊓ M ≤ W → ∀ v ∈ W, orderOf v = 2 →
      (∀ w ∈ W, v * w = w * v) → centralizer ({v} : Set G) ≤ M := by
  intro W hW hTW v hvW hv2 hvc'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := hstd.orderOf_x
  have hxW : x ∈ W := hTW ⟨hstd.x_mem_T, hxM⟩
  have hvM : v ∈ M := hW.le hvW
  have hvc : ∀ w ∈ W, w * v = v * w := fun w hw => (hvc' w hw).symm
  obtain ⟨hLtop, n, hn, ⟨eK⟩, ⟨eL⟩⟩ := halt
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    exact hn
  have hm : n + 4 = 9 ∨ n + 4 = 10 ∨ n + 4 = 11 := by omega
  let e₀ : Mb M ≃* alternatingGroup (Fin (n + 4)) :=
    ((MulEquiv.subgroupCongr hLtop).trans Subgroup.topEquiv).symm.trans eL
  have hAM : AModel (n + 4) := by
    rcases hn' with rfl | rfl | rfl
    · exact Mod9.amodel_nine
    · exact amodel_ten_of_eleven Mod11.amodel_eleven
    · exact Mod11.amodel_eleven
  have hxb2 : orderOf (barMk ↥M (⟨x, hxM⟩ : ↥M)) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk x hxM).trans hx2)
  have hvb2 : orderOf (barMk ↥M (⟨v, hvM⟩ : ↥M)) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk v hvM).trans hv2)
  have hMM : imgM M M = ⊤ := by
    unfold imgM
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.map_top_of_surjective _ barMk_surjective
  have hWb : Nat.card ↥(imgM M W) = 2 ^ (Nat.card (Mb M)).factorization 2 := by
    have := (isSylowOf_imgM_of_le (le_refl M) hW).card_eq
    rwa [hMM, Subgroup.card_top] at this
  have hvcb : ∀ w ∈ imgM M W, w * barMk ↥M (⟨v, hvM⟩ : ↥M) = barMk ↥M (⟨v, hvM⟩ : ↥M) * w := by
    intro w hw
    obtain ⟨m', hm', rfl⟩ := mem_imgM_iff.1 hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hvc _ hm')
  have hKC : K ≤ centralizer ({x} : Set G) := hstd.K_le_C
  have h5 := five_dvd_centralizer hn' hxM hKC eK
  obtain ⟨hx4, hv8⟩ := Th2.AltStd.alt_types hm e₀ hxb2 h5 hWb hvb2 hvcb
  have hKperf0 : Group.IsPerfect ↥K := by
    have h1 := ClassicalInvolution.LBalanceProof.isPerfect_of_isPComponent hstd.comp.2
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKC).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKC).surjective
  have hKperf : Group.IsPerfect ↥(imgM M K) := Group.IsPerfect.ofSurjective (toImgM_surjective hKM)
  have hKcard : Nat.card (alternatingGroup (Fin n)) ≤ Nat.card ↥(imgM M K) := by
    have h1 : Nat.card (↥(imgM M K) ⧸ pPrimeCore 2 ↥(imgM M K)) ∣ Nat.card ↥(imgM M K) :=
      Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    rw [Nat.card_congr eK.toEquiv.symm]
    exact Nat.le_of_dvd Nat.card_pos h1
  have hKx := imgM_comm hxM hKC
  obtain ⟨e, hKe, hnm⟩ := exists_std_iso (by omega : 5 ≤ n) e₀ hKperf hKcard hKx hx4
  have hx4e : numMoved ((e (barMk ↥M (⟨x, hxM⟩ : ↥M)) : alternatingGroup (Fin (n + 4))) :
      Perm (Fin (n + 4))) = 4 := (hnm _).trans hx4
  have hv8e : numMoved ((e (barMk ↥M (⟨v, hvM⟩ : ↥M)) : alternatingGroup (Fin (n + 4))) :
      Perm (Fin (n + 4))) = 8 := (hnm _).trans hv8
  obtain ⟨W', v', hv'M, hW', hxW', hv'W', hv'2, hv'c, ⟨c, hcM, hcv, hcx⟩, ⟨m, hmM, hmv⟩⟩ :=
    exists_conj_pair hAM e hxM hvM hx2 hv2 hW hvW hvc hx4e hv8e
  have hv'b2 : orderOf (barMk ↥M (⟨v', hv'M⟩ : ↥M)) = 2 :=
    orderOf_barMk ((Subgroup.orderOf_mk v' hv'M).trans hv'2)
  have hW'b : Nat.card ↥(imgM M W') = 2 ^ (Nat.card (Mb M)).factorization 2 := by
    have := (isSylowOf_imgM_of_le (le_refl M) hW').card_eq
    rwa [hMM, Subgroup.card_top] at this
  have hv'cb : ∀ w ∈ imgM M W', w * barMk ↥M (⟨v', hv'M⟩ : ↥M) =
      barMk ↥M (⟨v', hv'M⟩ : ↥M) * w := by
    intro w hw
    obtain ⟨m', hm', rfl⟩ := mem_imgM_iff.1 hw
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hv'c _ hm')
  obtain ⟨hncb, -, -⟩ := Th2.AltInv.alt_facts hm e₀ hxb2 h5 hW'b hv'b2 hv'cb
  have hF : ∀ g : G, g * x * g⁻¹ ∈ M → g ∈ M :=
    fusion_control hm e₀ hxM hv'M hx2 hv'2 h5 hW' hv'c hCx
  have hWG : IsSylowOf 2 W' ⊤ := isSylowOf_top_of_fusion hW' hxW' hF
  have hnc : ¬ IsConj x v' := by
    intro hxv
    obtain ⟨g, hg⟩ := isConj_iff.1 hxv
    have hgM : g ∈ M := hF g (hg ▸ hv'M)
    apply hncb
    refine isConj_iff.2 ⟨barMk ↥M ⟨g, hgM⟩, ?_⟩
    have h1 : (⟨g, hgM⟩ : ↥M) * ⟨x, hxM⟩ * (⟨g, hgM⟩ : ↥M)⁻¹ = ⟨v', hv'M⟩ := Subtype.ext hg
    rw [← map_inv, ← map_mul, ← map_mul, h1]
  have hWcard : Nat.card ↥W' = 2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    obtain ⟨eW⟩ := equiv_imgM hW'.le hW'.isPGroup
    rw [Nat.card_congr eW.toEquiv, hW'b, Nat.card_congr e₀.toEquiv]
  have hS128 : Nat.card ↥W' ≤ 128 := hWcard ▸ two_part_le hn'
  have hxz : IsConj x (x * v') := isConj_iff.2 ⟨c, hcx⟩
  have hsyl : IsSylowOf 2 (W'.subgroupOf M) ⊤ := by
    have h2 : IsSylowOf 2 ((W'.subgroupOf M).map M.subtype) ((⊤ : Subgroup ↥M).map M.subtype) := by
      rw [Subgroup.map_subgroupOf_eq_of_le hW'.le, Subgroup.map_top, Subgroup.range_subtype]
      exact hW'
    exact (isSylowOf_map_subtype_iff M).1 h2
  have hScard : Nat.card ↥(W'.subgroupOf M) ≤
      2 ^ (Nat.card (alternatingGroup (Fin (n + 4)))).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW'.le).toEquiv, hWcard]
  have hKe' : (((K.subgroupOf M).map (piO ↥M)).subgroupOf (⊤ : Subgroup (↥M ⧸ pPrimeCore 2 ↥M))).map
      (Subgroup.topEquiv.trans e).toMonoidHom = stdAlt n := by
    rw [← hKe]
    ext τ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.1, Subgroup.mem_subgroupOf.1 ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, Subgroup.mem_top a⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
  have hxx' : (⟨x, hxM⟩ : ↥M) ∈ Subgroup.zpowers (⟨x, hxM⟩ : ↥M) := Subgroup.mem_zpowers _
  have hQS : Subgroup.zpowers (⟨x, hxM⟩ : ↥M) ≤ W'.subgroupOf M :=
    Subgroup.zpowers_le.2 hxW'
  have hQK : ∀ q ∈ Subgroup.zpowers (⟨x, hxM⟩ : ↥M), ∀ k ∈ K.subgroupOf M,
      piO ↥M q * piO ↥M k = piO ↥M k * piO ↥M q := by
    intro q hq k hk
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    have hc' : Commute (piO ↥M k) (piO ↥M (⟨x, hxM⟩ : ↥M)) :=
      hKx (piO ↥M k) ⟨k, hk, rfl⟩
    rw [map_zpow]
    exact ((hc'.symm.zpow_left j).eq)
  have hxv'' : ¬ IsConj (⟨x, hxM⟩ : ↥M) ⟨v', hv'M⟩ := fun h =>
    hncb (by simpa using (barMk ↥M).map_isConj h)
  have hxz' : IsConj (⟨x, hxM⟩ : ↥M) (⟨x, hxM⟩ * ⟨v', hv'M⟩) :=
    isConj_iff.2 ⟨⟨c, hcM⟩, Subtype.ext hcx⟩
  have hti : TIMOutQ M W' x v' hxM hv'M :=
    ti_data_MQ hn' hAM (⊤ : Subgroup (↥M ⧸ pPrimeCore 2 ↥M)) (Subgroup.topEquiv.trans e)
      Subgroup.IsSubnormal.top hsyl hScard hKe' hQS hQK hxx'
      ((Subgroup.orderOf_mk x hxM).trans hx2) ((Subgroup.orderOf_mk v' hv'M).trans hv'2)
      hv'W' (fun s hs => Subtype.ext (hv'c _ hs)) hxv'' hxz'
  have hcv' := centralizer_v_le_of_gold hGold hN11a hN11b M W' x v' hxM hv'M hW'.le hxW' hWG hx2
    hv'2 hv'c hnc hF hS128 hti
  intro g hg
  have hgv : g * v = v * g := mem_centralizer_singleton_iff.1 hg
  have hmv' : v' = m⁻¹ * v * m := by
    calc v' = m⁻¹ * (m * v' * m⁻¹) * m := by group
      _ = m⁻¹ * v * m := by rw [hmv]
  have hc1 : m⁻¹ * g * m ∈ centralizer ({v'} : Set G) := by
    rw [mem_centralizer_singleton_iff, hmv']
    calc m⁻¹ * g * m * (m⁻¹ * v * m) = m⁻¹ * (g * v) * m := by group
      _ = m⁻¹ * (v * g) * m := by rw [hgv]
      _ = m⁻¹ * v * m * (m⁻¹ * g * m) := by group
  have hc2 := hcv' hc1
  have : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hmM hc2) (M.inv_mem hmM)

end CFSG.GH74.GLS.Th2.AltCv

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.P43f
  CFSG.GH74.GLS.Th2.P412 CFSG.GH74.GLS.C3.Layer1.Back CFSG.GH74.GLS.C3.Layer1.Bk
  CFSG.GH74.Uniqueness

theorem b_prop412a_Cv_of_gold (hZD : S_ZD) (hGold : GoldStmt)
    (hN11a : CFSG.Goldschmidt.S_N11a) (hN11b : CFSG.Goldschmidt.S_N11b) (hc5 : B_thm2_cent5) :
    B_prop412a_Cv := by
  intro G _ _ hG x y K T S hs h7 hQ4 hTS hQel hnt v hv2 hvS hvx
  obtain ⟨e7⟩ := h7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPd8 : IsD8 (T ⊓ K) := isD8_of_inf_alt7 hs.T_pGroup hs.sylow_P e7
  obtain ⟨D, hDP, hDel, hD4, -⟩ := hPd8.exists_four_containing (p := 1) (one_mem _) (mul_one 1)
  have hD2 : pRank 2 ↥D = 2 := by
    have h1 := card_eq_two_pow_pRank hDel
    rw [hD4] at h1
    have h2 : (2 : ℕ) ^ 2 = 2 ^ pRank 2 ↥D := by simpa using h1
    exact (Nat.pow_right_injective le_rfl h2).symm
  have hP2 : 2 ≤ pRank 2 ↥(T ⊓ K) := hD2.symm.le.trans (pRank_mono' hDP)
  obtain ⟨a, z, psi, F⟩ := exists_frame hc5 hG hs e7 hQ4 hTS hP2 hQel
  obtain ⟨s₁, hs₁, hs₁2, hs₁R⟩ := F.exists_invol_not_mem_R hG hs e7 hP2 hQ4
  have hvsq : v * v = 1 := by
    have h1 : v ^ 2 = 1 := by rw [← hv2]; exact pow_orderOf_eq_one v
    rwa [sq] at h1
  have hv1 : v ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv2
    omega
  have hvS' : v ∈ S := mem_S_of_commute hs.sylowS hvsq (fun s hs' => hvS s hs')
  have hvzx : v = z * x := F.eq_v_of_central hvS' hv1 (fun t ht => (hvS t ht).symm)
  subst hvzx
  have hR := F.R_four hG hs e7 hP2 hQ4
  have hs₁1 : s₁ ≠ 1 := fun h => hs₁R (h ▸ one_mem _)
  have hs₁z : s₁ ≠ z := fun h => hs₁R (h ▸ F.z_mem_four hR)
  have hint := F.Fv_inter hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R
  have hEq := F.Ev_eq_Esub hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R
  have hxv : ¬ IsConj x (z * x) :=
    F.not_isConj_v_of_Q hG hs e7 hP2 hQ4 ⟨F.x_mem_T, F.x_mem_CxK⟩ F.x_sq F.x_ne
  have hSC : S ≤ centralizer ({z * x} : Set G) := fun s hs' =>
    Subgroup.mem_centralizer_singleton_iff.2 (by
      have h1 := F.S_centralizes_v s hs'
      calc s * (z * x) = (s * (z * x) * s⁻¹) * s := by group
        _ = (z * x) * s := by rw [h1])
  have hxC : x ∈ centralizer ({z * x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 F.x_mem_Fv.1
  have hEel := F.Esub_el hs₁ hs₁2
  refine isSolvable_of_E8_data_gold hZD hGold hN11a hN11b (Zs := Fv x (z * x)) (S := S) (E := Esub x z a s₁)
    (Subgroup.mem_centralizer_singleton_iff.2 rfl) hxC hSC F.v_sq F.v_ne
    (fun c hc => Subgroup.mem_centralizer_singleton_iff.1 hc)
    (fun t ht => ht.2.1) (fun t ht h1 => F.x_ne (isConj_one_left.1 (h1 ▸ ht.2.2.1)))
    (fun h => hxv h.2.2.1)
    (fun t ht g hg => Fv_conj (Subgroup.mem_centralizer_singleton_iff.1 hg) ht)
    (fun t ht => Fv_mul_v F.v_sq ht) (hs.sylowS.of_le hSC le_top)
    ((F.Esub_le_T hs₁).trans F.core.T_le_S) (F.Esub_card hs₁ hs₁2 hs₁1 hs₁z)
    ((forall_of_isElementaryAbelian hEel).1) ((forall_of_isElementaryAbelian hEel).2)
    (Subgroup.mul_mem _ (z_mem_Esub x z a s₁) (x_mem_Esub x z a s₁)) ?_ hint F.x_mem_Fv
    (x_mem_Esub x z a s₁) ?_ F.card_S_le ?_ ?_ (F.card_CS_le hs₁ hs₁1 hs₁z)
  ·
    intro s hs' e he
    by_cases he1 : e = 1
    · rw [he1]
      simp
    by_cases hev : e = z * x
    · rw [hev, F.S_centralizes_v s hs']
      exact Subgroup.mul_mem _ (z_mem_Esub x z a s₁) (x_mem_Esub x z a s₁)
    have heS : e ∈ S := (F.Esub_le_T hs₁).trans F.core.T_le_S he
    have heF : e ∈ Fv x (z * x) := (hint e heS).2 ⟨he, he1, hev⟩
    have hsF : s * e * s⁻¹ ∈ Fv x (z * x) := Fv_conj (Subgroup.mem_centralizer_singleton_iff.1 (hSC hs')) heF
    have hsS : s * e * s⁻¹ ∈ S := S.mul_mem (S.mul_mem hs' heS) (S.inv_mem hs')
    exact ((hint _ hsS).1 hsF).1
  ·
    intro t ht
    obtain ⟨c, hcv, hc⟩ := F.exists_conj_of_Fv hG hs e7 hP2 hQ4 ht.1 ht.2.2.1 ht.2.2.2
    exact ⟨c, Subgroup.mem_centralizer_singleton_iff.2 hcv, hc⟩
  · exact ⟨s₁, F.core.T_le_S hs₁.1, hs₁2, F.s1_not_mem_Esub hG hs e7 hP2 hQ4 hs₁ hs₁2 hs₁R⟩
  · intro s hs' hc hs2 hs1
    exact F.eq_v_of_central hs' hs1 hc

theorem b_thm2_p85_alt_cv_of_gold
    (hGold : Th2.P412.GoldStmt)
    (hN11a : CFSG.Goldschmidt.S_N11a) (hN11b : CFSG.Goldschmidt.S_N11b) :
    B_thm2_p85_alt_cv := by
  intro G _ _ x y K T S M L hstruct halt hCx W hW hTW v hv hv2 hvc
  have hstd : Th2Std x y K T S := hstruct.choice.std
  have hxM : x ∈ M := hCx (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  exact Th2.AltCv.alt_cv_of_gold hGold hN11a hN11b hstd hstruct.KM hxM halt hCx W hW hTW v hv hv2 hvc

end CFSG.GH74.GLS
