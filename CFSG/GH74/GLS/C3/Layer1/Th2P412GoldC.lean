module

public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldTrans
public import CFSG.GH74.GLS.C3.Layer1.Th2P412GoldX
public import CFSG.GH74.GLS.C3.Layer1.Th2P412Loc
public import CFSG.GH74.GLS.C3.Layer2.L4End

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Goldschmidt CFSG.GH74.GLS.C3.Layer2.L4

structure TIData0 {C : Type} [Group C] (v : C) (Zs : Set C) (S E : Subgroup C) (x : C) : Prop where
  v_sq : v * v = 1
  v_ne : v ≠ 1
  v_comm : ∀ c : C, c * v = v * c
  Z_sq : ∀ z ∈ Zs, z * z = 1
  Z_ne : ∀ z ∈ Zs, z ≠ 1
  v_nmem : v ∉ Zs
  Z_conj : ∀ z ∈ Zs, ∀ g : C, g * z * g⁻¹ ∈ Zs
  Z_mul_v : ∀ z ∈ Zs, z * v ∈ Zs
  sylow : IsSylowOf 2 S ⊤
  E_le : E ≤ S
  E_card : Nat.card E = 8
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  E_sq : ∀ a ∈ E, a * a = 1
  v_mem : v ∈ E
  S_norm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E
  Z_inter : ∀ y ∈ S, (y ∈ Zs ↔ (y ∈ E ∧ y ≠ 1 ∧ y ≠ v))
  x_Z : x ∈ Zs
  x_E : x ∈ E
  Z_single : ∀ z ∈ Zs, ∃ c : C, c * x * c⁻¹ = z

namespace TIData0

variable {C : Type} [Group C] {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

theorem zpowers_le_E (h : TIData0 v Zs S E x) : zpowers v ≤ E := zpowers_le.2 h.v_mem

theorem zpowers_le_S (h : TIData0 v Zs S E x) : zpowers v ≤ S := h.zpowers_le_E.trans h.E_le

theorem zpowers_normal (h : TIData0 v Zs S E x) : (zpowers v).Normal := by
  refine ⟨fun a ha g => ?_⟩
  rcases (mem_zpowers_iff_of_mul_self h.v_sq).1 ha with h1 | h1
  · rw [h1]; simp
  · have : g * v * g⁻¹ = v := by rw [h.v_comm g]; group
    rw [h1, this]; exact mem_zpowers _

theorem zpowers_le_center (h : TIData0 v Zs S E x) : zpowers v ≤ center C := by
  rw [zpowers_le, Subgroup.mem_center_iff]
  exact fun c => h.v_comm c

theorem exists_conj_mul_v (h : TIData0 v Zs S E x) {e : C} (he : e ∈ E) (he1 : e ≠ 1)
    (hev : e ≠ v) : ∃ c : C, c * e * c⁻¹ = e * v := by
  have heZ : e ∈ Zs := (h.Z_inter e (h.E_le he)).2 ⟨he, he1, hev⟩
  have hevZ : e * v ∈ Zs := h.Z_mul_v e heZ
  obtain ⟨c₁, hc₁⟩ := h.Z_single e heZ
  obtain ⟨c₂, hc₂⟩ := h.Z_single (e * v) hevZ
  refine ⟨c₂ * c₁⁻¹, ?_⟩
  have h1 : c₁⁻¹ * e * c₁ = x := by rw [← hc₁]; group
  calc (c₂ * c₁⁻¹) * e * (c₂ * c₁⁻¹)⁻¹ = c₂ * (c₁⁻¹ * e * c₁) * c₂⁻¹ := by group
    _ = c₂ * x * c₂⁻¹ := by rw [h1]
    _ = e * v := hc₂

end TIData0

section Main

variable {C : Type} [Group C] [Finite C] {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

theorem gold_normal_EO
    (hGold : GoldStmt) (hN11a : S_N11a) (hN11b : S_N11b)
    (h : TIData0 v Zs S E x) (hS128 : Nat.card S ≤ 128)
    (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E) :
    ∀ c : C, ∀ e ∈ E, ∃ e' ∈ E, ∃ o ∈ pPrimeCore 2 C, c * e * c⁻¹ = e' * o := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVn : (zpowers v).Normal := h.zpowers_normal
  set π₁ : C →* C ⧸ zpowers v := QuotientGroup.mk' (zpowers v) with hπ₁
  have hπ₁surj : Function.Surjective π₁ := QuotientGroup.mk'_surjective _
  have hπ₁v : π₁ v = 1 := (QuotientGroup.eq_one_iff v).2 (mem_zpowers v)
  have hπ₁ker : ∀ y : C, π₁ y = 1 → y ∈ zpowers v := fun y hy => (QuotientGroup.eq_one_iff y).1 hy
  have hmemS : ∀ y : C, π₁ y ∈ S.map π₁ → y ∈ S := by
    rintro y ⟨s, hs, hsy⟩
    have hsy' : (QuotientGroup.mk s : C ⧸ zpowers v) = QuotientGroup.mk y := hsy
    have h1 : s⁻¹ * y ∈ zpowers v := QuotientGroup.eq.1 hsy'
    have : y = s * (s⁻¹ * y) := by group
    rw [this]
    exact S.mul_mem hs (h.zpowers_le_S h1)
  have hmemE : ∀ y : C, π₁ y ∈ E.map π₁ → y ∈ E := by
    rintro y ⟨s, hs, hsy⟩
    have hsy' : (QuotientGroup.mk s : C ⧸ zpowers v) = QuotientGroup.mk y := hsy
    have h1 : s⁻¹ * y ∈ zpowers v := QuotientGroup.eq.1 hsy'
    have : y = s * (s⁻¹ * y) := by group
    rw [this]
    exact E.mul_mem hs (h.zpowers_le_E h1)
  obtain ⟨-, hSp, hSidx⟩ := isSylowOf_iff.1 h.sylow
  have hSX_p : IsPGroup 2 ↥(S.map π₁) := hSp.map _
  have hSX_idx : ¬ 2 ∣ (S.map π₁).index := by
    rw [Subgroup.relIndex_top_right] at hSidx
    exact fun hdvd => hSidx (hdvd.trans (Subgroup.index_map_dvd S hπ₁surj))
  let SX : Sylow 2 (C ⧸ zpowers v) := hSX_p.toSylow hSX_idx
  have hSX : (SX : Subgroup (C ⧸ zpowers v)) = S.map π₁ := IsPGroup.toSylow_coe _ _
  set A : Subgroup (C ⧸ zpowers v) := E.map π₁ with hA
  have hAS : A ≤ (SX : Subgroup (C ⧸ zpowers v)) := by
    rw [hSX]; exact Subgroup.map_mono h.E_le
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩
    simp only [← map_mul]
    rw [h.E_comm e₁ he₁ e₂ he₂]
  have hAsq : ∀ a ∈ A, a * a = 1 := by
    rintro _ ⟨e, he, rfl⟩
    rw [← map_mul, h.E_sq e he, map_one]
  have hA4 : Nat.card A = 4 := by
    have h1 : Nat.card (E.map π₁) * 2 = Nat.card E :=
      card_map_mk_mul_two (v := v) h.v_sq h.v_ne E h.zpowers_le_E
    rw [h.E_card] at h1
    show Nat.card (E.map π₁) = 4
    omega
  have hAne : ∀ e ∈ E, π₁ e ≠ 1 → e ≠ 1 ∧ e ≠ v := by
    intro e he hne
    exact ⟨fun h1 => hne (by rw [h1, map_one]), fun h1 => hne (by rw [h1]; exact hπ₁v)⟩
  have hclosedX : ∀ a ∈ A, ∀ g : C ⧸ zpowers v,
      g⁻¹ * a * g ∈ (SX : Subgroup (C ⧸ zpowers v)) → g⁻¹ * a * g ∈ A := by
    rintro _ ⟨e, he, rfl⟩ g hg
    obtain ⟨c, rfl⟩ := hπ₁surj g
    have h1 : π₁ (c⁻¹ * e * c) ∈ S.map π₁ := by
      rw [map_mul, map_mul, map_inv]
      rw [hSX] at hg
      exact hg
    have h2 : c⁻¹ * e * c ∈ S := hmemS _ h1
    by_cases he1 : e = 1
    · rw [he1]
      refine ⟨1, one_mem _, ?_⟩
      simp
    by_cases hev : e = v
    · rw [hev]
      refine ⟨v, h.v_mem, ?_⟩
      have : c⁻¹ * v * c = v := by
        have h5 := h.v_comm c⁻¹
        calc c⁻¹ * v * c = v * c⁻¹ * c := by rw [h5]
          _ = v := by group
      rw [← map_inv, ← map_mul, ← map_mul, this]
    · have heZ : e ∈ Zs := (h.Z_inter e (h.E_le he)).2 ⟨he, he1, hev⟩
      have h3 : c⁻¹ * e * c ∈ Zs := by
        have := h.Z_conj e heZ c⁻¹
        simpa using this
      have h4 := ((h.Z_inter _ h2).1 h3).1
      refine ⟨c⁻¹ * e * c, h4, ?_⟩
      rw [map_mul, map_mul, map_inv]
  have htransX : ∀ a ∈ A, ∀ b ∈ A, a ≠ 1 → b ≠ 1 → ∃ g : C ⧸ zpowers v, g⁻¹ * a * g = b := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩ ha hb
    obtain ⟨he1, hev⟩ := hAne e he ha
    obtain ⟨he1', hev'⟩ := hAne e' he' hb
    have heZ : e ∈ Zs := (h.Z_inter e (h.E_le he)).2 ⟨he, he1, hev⟩
    have heZ' : e' ∈ Zs := (h.Z_inter e' (h.E_le he')).2 ⟨he', he1', hev'⟩
    obtain ⟨c₁, hc₁⟩ := h.Z_single e heZ
    obtain ⟨c₂, hc₂⟩ := h.Z_single e' heZ'
    refine ⟨π₁ (c₁ * c₂⁻¹), ?_⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [← hc₁, ← hc₂]
    group
  have hgold := gold_analysis hGold hN11a hN11b SX A hAS hAcomm hAsq hA4 hclosedX htransX
  rw [hSX] at hgold
  set M : Subgroup (C ⧸ zpowers v) := Subgroup.normalClosure (A : Set (C ⧸ zpowers v)) with hM
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hAM : A ≤ M := Subgroup.subset_normalClosure
  rcases hgold with ⟨Q, hQn, hAQ, Nn, hNn, hNodd, hQle⟩ | hSM | ⟨h64, hinv⟩
  ·
    intro c e he
    set P : Subgroup C := Nn.comap π₁ with hPdef
    have hPn : P.Normal := hNn.comap π₁
    have hvP : zpowers v ≤ P := by
      rw [zpowers_le]
      show π₁ v ∈ Nn
      rw [hπ₁v]
      exact Nn.one_mem
    have hodd : Odd ((zpowers v).relIndex P) := by
      have h2 := Subgroup.relIndex_comap (⊥ : Subgroup (C ⧸ zpowers v)) π₁ P
      rw [MonoidHom.comap_bot, QuotientGroup.ker_mk'] at h2
      rw [h2, hPdef, Subgroup.map_comap_eq_self_of_surjective hπ₁surj Nn,
        Subgroup.relIndex_bot_left]
      exact hNodd
    have hle : P ≤ zpowers v ⊔ pPrimeCore 2 C :=
      le_sup_pPrimeCore_of_central_sylow h.zpowers_le_center
        (TIData.isPGroup_zpowers h.v_sq) hvP hodd
    have hcX : π₁ (c * e * c⁻¹) ∈ Q := by
      have := hQn.conj_mem (π₁ e) (hAQ ⟨e, he, rfl⟩) (π₁ c)
      simpa [map_mul, map_inv] using this
    have hcX' : π₁ (c * e * c⁻¹) ∈ A ⊔ Nn := hQle hcX
    rw [Subgroup.mem_sup_of_normal_right] at hcX'
    obtain ⟨a, ha, n, hn, han⟩ := hcX'
    obtain ⟨e₀, he₀, rfl⟩ := ha
    have h3 : e₀⁻¹ * (c * e * c⁻¹) ∈ P := by
      show π₁ (e₀⁻¹ * (c * e * c⁻¹)) ∈ Nn
      rw [map_mul, map_inv, ← han]
      simpa using hn
    have h4 : e₀⁻¹ * (c * e * c⁻¹) ∈ zpowers v ⊔ pPrimeCore 2 C := hle h3
    have h5 : c * e * c⁻¹ ∈ E ⊔ pPrimeCore 2 C := by
      have : c * e * c⁻¹ = e₀ * (e₀⁻¹ * (c * e * c⁻¹)) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left he₀)
        ((sup_le_sup_right h.zpowers_le_E (pPrimeCore 2 C)) h4)
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right.1 h5)
    exact ⟨y, hy, z, hz, hyz.symm⟩
  ·
    set L : Subgroup C := M.comap π₁ with hL
    have hLn : L.Normal := hMn.comap π₁
    have hvL : v ∈ L := by
      show π₁ v ∈ M
      rw [hπ₁v]
      exact M.one_mem
    have hEL : E ≤ L := fun e he => hAM ⟨e, he, rfl⟩
    have hEeq : E = S ⊓ L := by
      apply le_antisymm
      · exact le_inf h.E_le hEL
      · rintro y ⟨hyS, hyL⟩
        have h1 : π₁ y ∈ S.map π₁ ⊓ M := ⟨⟨y, hyS, rfl⟩, hyL⟩
        rw [hSM] at h1
        exact hmemE y h1
    have hSylL : IsSylowOf 2 E L := by
      rw [hEeq]
      exact h.sylow.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.2 hLn).ge
    have hLle : L ≤ E ⊔ pPrimeCore 2 C :=
      le_sup_pPrimeCore_of_abelian_sylow hSylL h.E_comm h.v_mem h.v_comm h.v_sq h.v_ne
        (fun e he he1 hev => h.exists_conj_mul_v he he1 hev)
    intro c e he
    have hcL : c * e * c⁻¹ ∈ L := hLn.conj_mem e (hEL he) c
    obtain ⟨y, hy, z, hz, hyz⟩ := (Subgroup.mem_sup_of_normal_right.1 (hLle hcL))
    exact ⟨y, hy, z, hz, hyz.symm⟩
  ·
    exfalso
    have hSXcard : Nat.card (S.map π₁) ≤ 64 := by
      have h1 : Nat.card (S.map π₁) * 2 = Nat.card S :=
        card_map_mk_mul_two (v := v) h.v_sq h.v_ne S h.zpowers_le_S
      omega
    have hSXM : S.map π₁ ⊓ M = S.map π₁ :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
    obtain ⟨s, hsS, hs2, hsE⟩ := hex
    have hs_in : π₁ s ∈ S.map π₁ ⊓ M := by
      rw [hSXM]
      exact ⟨s, hsS, rfl⟩
    have hπs2 : π₁ s * π₁ s = 1 := by rw [← map_mul, hs2, map_one]
    exact hsE (hmemE s (hinv _ hs_in hπs2))

end Main

end CFSG.GH74.GLS.Th2.P412
