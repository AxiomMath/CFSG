module

public import CFSG.GH74.Tits83.Octagon

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

namespace TitsSystem

variable {G : Type u} [Group G] {n : ℕ}

@[expose] def normClosure2 (A B X : Subgroup G) : Subgroup G :=
  sInf {Y : Subgroup G | X ≤ Y ∧ A ≤ Subgroup.normalizer (Y : Set G) ∧
    B ≤ Subgroup.normalizer (Y : Set G)}

variable (T : TitsSystem G n)

private theorem mu_n_eq_mu_zero_nu (hn : 3 ≤ n) {u : G} (hu : u ∈ T.U n) (hu1 : u ≠ 1) :
    T.mu n u = T.mu 0 (T.nu n u) := by
  have h := (T.mu_nu hn (i := n) hu hu1).1
  have hp : T.mu ((n : ℤ) + n) (T.nu n u) = T.mu 0 (T.nu n u) := by
    have := T.mu_add_two_mul hn 0 1 (T.nu n u)
    rwa [show (0 : ℤ) + 2 * n * 1 = (n : ℤ) + n by ring] at this
  rw [← h, hp]

private def Wmid (i : ℤ) : Subgroup G := win T.U (i + 1) (n - i - 1)

private def Kleft (i : ℤ) : Subgroup G := win T.U 1 (n - i - 1)

private def Kright (i : ℤ) : Subgroup G := win T.U (i + 1) (n - 1)

private def Aleft (i : ℤ) (Vni : Subgroup G) : Subgroup G := Kleft T i ⊔ Vni

private def Bright (i : ℤ) (Vi : Subgroup G) : Subgroup G := Vi ⊔ Kright T i

private def Vsub (i : ℤ) (Vi Vni : Subgroup G) : Subgroup G := Vi ⊔ Wmid T i ⊔ Vni

private theorem Vni_le_normalizer_Kleft {i : ℤ} {Vni : Subgroup G} (hi : 0 < i)
    (hVni : Vni ≤ T.U (n - i)) : Vni ≤ Subgroup.normalizer (Kleft T i : Set G) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun c hc => ?_
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
  have hc' : c ∈ T.U (n - i) := hVni hc
  obtain ⟨f, hf, hfx⟩ := (T.mem_win_iff_prod (a := 1) (b := n - i - 1) (by omega)).1 hx
  rw [hfx]
  have hprod : c * ((intList 1 (n - i - 1)).map f).prod * c⁻¹ =
      ((intList 1 (n - i - 1)).map (fun k => c * f k * c⁻¹)).prod := by
    have h1 : c * ((intList 1 (n - i - 1)).map f).prod * c⁻¹ =
        (MulAut.conj c).toMonoidHom ((intList 1 (n - i - 1)).map f).prod := rfl
    rw [h1, map_list_prod, List.map_map]
    rfl
  rw [hprod]
  refine (Kleft T i).list_prod_mem ?_
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  have hk' := mem_intList_iff.1 hk
  have hfk : f k ∈ T.U k := hf k hk
  have hle : T.U k ≤ Kleft T i := le_iSup₂_of_le k ⟨hk'.1, hk'.2⟩ le_rfl
  have hcomm : ⁅c, f k⁆ ∈ Kleft T i := by
    have h := T.comm k (n - i) (by omega) (by omega) (f k) hfk c hc'
    have hinv := (⨆ t ∈ Set.Ioo k (n - i), T.U t).inv_mem h
    have e : ⁅c, f k⁆ = ⁅f k, c⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine SetLike.le_def.mp ?_ hinv
    refine iSup₂_le fun t ht => ?_
    have ht' : k < t ∧ t < n - i := ht
    exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
  have hform : c * f k * c⁻¹ = ⁅c, f k⁆ * f k := by
    simp only [commutatorElement_def]
    group
  rw [hform]
  exact (Kleft T i).mul_mem hcomm (hle hfk)

private theorem Vi_le_normalizer_Kright {i : ℤ} {Vi : Subgroup G} (hi : 0 < i)
    (hVi : Vi ≤ T.U i) : Vi ≤ Subgroup.normalizer (Kright T i : Set G) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun c hc => ?_
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
  have hc' : c ∈ T.U i := hVi hc
  obtain ⟨f, hf, hfx⟩ := (T.mem_win_iff_prod (a := i + 1) (b := n - 1) (by omega)).1 hx
  rw [hfx]
  have hprod : c * ((intList (i + 1) (n - 1)).map f).prod * c⁻¹ =
      ((intList (i + 1) (n - 1)).map (fun k => c * f k * c⁻¹)).prod := by
    have h1 : c * ((intList (i + 1) (n - 1)).map f).prod * c⁻¹ =
        (MulAut.conj c).toMonoidHom ((intList (i + 1) (n - 1)).map f).prod := rfl
    rw [h1, map_list_prod, List.map_map]
    rfl
  rw [hprod]
  refine (Kright T i).list_prod_mem ?_
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  have hk' := mem_intList_iff.1 hk
  have hfk : f k ∈ T.U k := hf k hk
  have hle : T.U k ≤ Kright T i := le_iSup₂_of_le k ⟨hk'.1, hk'.2⟩ le_rfl
  have hcomm : ⁅c, f k⁆ ∈ Kright T i := by
    have h := T.comm i k (by omega) (by omega) c hc' (f k) hfk
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun t ht => ?_
    have ht' : i < t ∧ t < k := ht
    exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
  have hform : c * f k * c⁻¹ = ⁅c, f k⁆ * f k := by
    simp only [commutatorElement_def]
    group
  rw [hform]
  exact (Kright T i).mul_mem hcomm (hle hfk)

private theorem Vni_le_normalizer_Wmid {i : ℤ} {Vni : Subgroup G} (hi : 0 < i)
    (hVni : Vni ≤ T.U (n - i)) : Vni ≤ Subgroup.normalizer (Wmid T i : Set G) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun c hc => ?_
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
  have hc' : c ∈ T.U (n - i) := hVni hc
  obtain ⟨f, hf, hfx⟩ := (T.mem_win_iff_prod (a := i + 1) (b := n - i - 1) (by omega)).1 hx
  rw [hfx]
  have hprod : c * ((intList (i + 1) (n - i - 1)).map f).prod * c⁻¹ =
      ((intList (i + 1) (n - i - 1)).map (fun k => c * f k * c⁻¹)).prod := by
    have h1 : c * ((intList (i + 1) (n - i - 1)).map f).prod * c⁻¹ =
        (MulAut.conj c).toMonoidHom ((intList (i + 1) (n - i - 1)).map f).prod := rfl
    rw [h1, map_list_prod, List.map_map]
    rfl
  rw [hprod]
  refine (Wmid T i).list_prod_mem ?_
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hy
  have hk' := mem_intList_iff.1 hk
  have hfk : f k ∈ T.U k := hf k hk
  have hle : T.U k ≤ Wmid T i := le_iSup₂_of_le k ⟨hk'.1, hk'.2⟩ le_rfl
  have hcomm : ⁅c, f k⁆ ∈ Wmid T i := by
    have h := T.comm k (n - i) (by omega) (by omega) (f k) hfk c hc'
    have hinv := (⨆ t ∈ Set.Ioo k (n - i), T.U t).inv_mem h
    have e : ⁅c, f k⁆ = ⁅f k, c⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    refine SetLike.le_def.mp ?_ hinv
    refine iSup₂_le fun t ht => ?_
    have ht' : k < t ∧ t < n - i := ht
    exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
  have hform : c * f k * c⁻¹ = ⁅c, f k⁆ * f k := by
    simp only [commutatorElement_def]
    group
  rw [hform]
  exact (Wmid T i).mul_mem hcomm (hle hfk)

private theorem Vi_le_normalizer_Wmid {i : ℤ} {Vi : Subgroup G} (hi : 0 < i)
    (hVi : Vi ≤ T.U i) : Vi ≤ Subgroup.normalizer (Wmid T i : Set G) := by
  have h := (T.le_normalizer_win (a := i + 1) (b := n - i - 1) (by omega)).1
  have h' : T.U i ≤ Subgroup.normalizer (Wmid T i : Set G) := by
    simpa [Wmid] using h
  exact hVi.trans h'

private theorem Vi_le_normalizer_Wmid_sup_Vni {i : ℤ} {Vi Vni : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i)) :
    Vi ≤ Subgroup.normalizer ((Wmid T i ⊔ Vni : Subgroup G) : Set G) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le
    (A := Vi) (M := Wmid T i ⊔ Vni) fun c hc => ?_
  rw [Subgroup.map_sup]
  refine sup_le ?_ ?_
  · have h := Vi_le_normalizer_Wmid T hi hVi hc
    exact (CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.1 h).le.trans
      (le_sup_left : Wmid T i ≤ Wmid T i ⊔ Vni)
  · refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
    have hx' : x ∈ T.U (n - i) := hVni hx
    have hcomm : ⁅c, x⁆ ∈ Wmid T i := by
      have h := T.comm i (n - i) (by omega) (by omega) c (hVi hc) x hx'
      have h' : c * x * c⁻¹ * x⁻¹ ∈ Wmid T i := by
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun t ht => ?_
        have ht' : i < t ∧ t < n - i := ht
        exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
      simpa only [commutatorElement_def] using h'
    have hform : c * x * c⁻¹ = ⁅c, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (Wmid T i ⊔ Vni).mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hx)

private theorem coe_Vsub {i : ℤ} {Vi Vni : Subgroup G} (hi : 0 < i) (hi2 : 2 * i < n)
    (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i)) :
    ((Vsub T i Vi Vni : Subgroup G) : Set G) =
      (Vi : Set G) * (Wmid T i : Set G) * (Vni : Set G) := by
  have hVniW := Vni_le_normalizer_Wmid T hi hVni
  have hViM := Vi_le_normalizer_Wmid_sup_Vni T hi hi2 hVi hVni
  rw [Vsub, sup_assoc]
  change ((Vi ⊔ (Wmid T i ⊔ Vni) : Subgroup G) : Set G) =
    (Vi : Set G) * (Wmid T i : Set G) * (Vni : Set G)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right Vi (Wmid T i ⊔ Vni) hViM]
  rw [Subgroup.coe_mul_of_right_le_normalizer_left (Wmid T i) Vni hVniW]
  rw [mul_assoc]

private theorem sup_inf_assoc_of_normalizes {A B C : Subgroup G} (hAC : A ≤ C)
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) : (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  apply le_antisymm
  · intro x hx
    have hxAB : x ∈ A ⊔ B := hx.1
    have hxC : x ∈ C := hx.2
    have hprod : ((A ⊔ B : Subgroup G) : Set G) = (A : Set G) * (B : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A B hAB
    have hxAB' : x ∈ ((A ⊔ B : Subgroup G) : Set G) := hxAB
    rw [hprod] at hxAB'
    obtain ⟨a, ha, b, hb, rfl⟩ := hxAB'
    have hbC : b ∈ C := by
      have h : a⁻¹ * (a * b) ∈ C := C.mul_mem (C.inv_mem (hAC ha)) hxC
      simpa [mul_assoc] using h
    exact (A ⊔ B ⊓ C).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hb, hbC⟩)
  · refine sup_le (le_inf le_sup_left hAC) ?_
    exact le_inf (inf_le_left.trans le_sup_right) inf_le_right

private theorem Aleft_inf_Bright_eq_Vsub {i : ℤ} {Vi Vni : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i)) :
    Aleft T i Vni ⊓ Bright T i Vi = Vsub T i Vi Vni := by
  have hVniKright : Vni ≤ Kright T i :=
    hVni.trans (le_iSup₂_of_le (n - i) ⟨by omega, by omega⟩ le_rfl)
  have hVniB : Vni ≤ Bright T i Vi := hVniKright.trans le_sup_right
  have hViKleft : Vi ≤ Kleft T i :=
    hVi.trans (le_iSup₂_of_le i ⟨by omega, by omega⟩ le_rfl)
  have h1 : (Vni ⊔ Kleft T i) ⊓ Bright T i Vi =
      Vni ⊔ (Kleft T i ⊓ Bright T i Vi) :=
    sup_inf_assoc_of_normalizes hVniB (Vni_le_normalizer_Kleft T hi hVni)
  have h2 : Kleft T i ⊓ Bright T i Vi = Vi ⊔ (Kleft T i ⊓ Kright T i) := by
    calc Kleft T i ⊓ Bright T i Vi = (Vi ⊔ Kright T i) ⊓ Kleft T i := by
          rw [Bright, inf_comm]
      _ = Vi ⊔ (Kright T i ⊓ Kleft T i) :=
          sup_inf_assoc_of_normalizes hViKleft (Vi_le_normalizer_Kright T hi hVi)
      _ = Vi ⊔ (Kleft T i ⊓ Kright T i) := by rw [inf_comm]
  have hK1K2 : Kleft T i ⊓ Kright T i = Wmid T i := by
    simp only [Kleft, Kright, Wmid]
    rw [T.win_inf_win (a := 1) (b := n - i - 1) (c := i + 1) (d := n - 1) (by omega)]
    congr 2 <;> omega
  rw [Aleft, sup_comm (Kleft T i) Vni, h1, h2, hK1K2, Vsub]
  ac_rfl

private theorem Vsub_map_conj_le_Aleft {i : ℤ} {Vi Vni : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i)) {g : G}
    (hg : g ∈ T.U 0) :
    (Vsub T i Vi Vni).map (MulAut.conj g).toMonoidHom ≤ Aleft T i Vni := by
  have hViKleft : Vi ≤ Kleft T i :=
    hVi.trans (le_iSup₂_of_le i ⟨by omega, by omega⟩ le_rfl)
  have hViMap : Vi.map (MulAut.conj g).toMonoidHom ≤ Kleft T i := by
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun a ha => ?_
    have ha' : a ∈ T.U i := hVi ha
    have hcomm : ⁅g, a⁆ ∈ Kleft T i := by
      have h := T.comm 0 i hi (by omega) g hg a ha'
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun t ht => ?_
      have ht' : 0 < t ∧ t < i := ht
      exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
    have hform : g * a * g⁻¹ = ⁅g, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (Kleft T i).mul_mem hcomm (hViKleft ha)
  have hWMap : (Wmid T i).map (MulAut.conj g).toMonoidHom ≤ Kleft T i := by
    simp only [Wmid, win, Subgroup.map_iSup]
    refine iSup₂_le fun k hk => ?_
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
    have hk' : i + 1 ≤ k ∧ k ≤ n - i - 1 := hk
    have hcomm : ⁅g, x⁆ ∈ Kleft T i := by
      have h := T.comm 0 k (by omega) (by omega) g hg x hx
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun t ht => ?_
      have ht' : 0 < t ∧ t < k := ht
      exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
    have hform : g * x * g⁻¹ = ⁅g, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    refine (Kleft T i).mul_mem hcomm ?_
    exact (le_iSup₂_of_le k ⟨by omega, hk'.2⟩ le_rfl : T.U k ≤ Kleft T i) hx
  have hVniMap : Vni.map (MulAut.conj g).toMonoidHom ≤ Aleft T i Vni := by
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun c hc => ?_
    have hc' : c ∈ T.U (n - i) := hVni hc
    have hcomm : ⁅g, c⁆ ∈ Kleft T i := by
      have h := T.comm 0 (n - i) (by omega) (by omega) g hg c hc'
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun t ht => ?_
      have ht' : 0 < t ∧ t < n - i := ht
      exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
    have hform : g * c * g⁻¹ = ⁅g, c⁆ * c := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (Aleft T i Vni).mul_mem (Subgroup.mem_sup_left hcomm) (Subgroup.mem_sup_right hc)
  rw [Vsub, Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le (sup_le (hViMap.trans le_sup_left) (hWMap.trans le_sup_left)) hVniMap

private theorem Vsub_map_conj_le_Bright {i : ℤ} {Vi Vni : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i)) {g : G}
    (hg : g ∈ T.U n) :
    (Vsub T i Vi Vni).map (MulAut.conj g).toMonoidHom ≤ Bright T i Vi := by
  have hViMap : Vi.map (MulAut.conj g).toMonoidHom ≤ Bright T i Vi := by
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun a ha => ?_
    have ha' : a ∈ T.U i := hVi ha
    have hcomm : ⁅g, a⁆ ∈ Kright T i := by
      have h := T.comm i n (by omega) (by omega) a ha' g hg
      have h' : a * g * a⁻¹ * g⁻¹ ∈ Kright T i := by
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun t ht => ?_
        have ht' : i < t ∧ t < n := ht
        exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
      have e : ⁅g, a⁆ = ⁅a, g⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      simpa only [commutatorElement_def] using (Kright T i).inv_mem h'
    have hform : g * a * g⁻¹ = ⁅g, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (Bright T i Vi).mul_mem
      ((le_sup_right : Kright T i ≤ Vi ⊔ Kright T i) hcomm)
      ((le_sup_left : Vi ≤ Vi ⊔ Kright T i) ha)
  have hWMap : (Wmid T i).map (MulAut.conj g).toMonoidHom ≤ Bright T i Vi := by
    simp only [Wmid, win, Subgroup.map_iSup]
    refine iSup₂_le fun k hk => ?_
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun x hx => ?_
    have hk' : i + 1 ≤ k ∧ k ≤ n - i - 1 := hk
    have hcomm : ⁅g, x⁆ ∈ Kright T i := by
      have h := T.comm k n (by omega) (by omega) x hx g hg
      have h' : x * g * x⁻¹ * g⁻¹ ∈ Kright T i := by
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun t ht => ?_
        have ht' : k < t ∧ t < n := ht
        exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
      have e : ⁅g, x⁆ = ⁅x, g⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      simpa only [commutatorElement_def] using (Kright T i).inv_mem h'
    have hform : g * x * g⁻¹ = ⁅g, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (Bright T i Vi).mul_mem
      ((le_sup_right : Kright T i ≤ Vi ⊔ Kright T i) hcomm)
      ((le_sup_right : Kright T i ≤ Vi ⊔ Kright T i)
        ((le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl : T.U k ≤ Kright T i) hx))
  have hVniMap : Vni.map (MulAut.conj g).toMonoidHom ≤ Bright T i Vi := by
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun c hc => ?_
    have hc' : c ∈ T.U (n - i) := hVni hc
    have hcomm : ⁅g, c⁆ ∈ Kright T i := by
      have h := T.comm (n - i) n (by omega) (by omega) c hc' g hg
      have h' : c * g * c⁻¹ * g⁻¹ ∈ Kright T i := by
        refine SetLike.le_def.mp ?_ h
        refine iSup₂_le fun t ht => ?_
        have ht' : n - i < t ∧ t < n := ht
        exact le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
      have e : ⁅g, c⁆ = ⁅c, g⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      simpa only [commutatorElement_def] using (Kright T i).inv_mem h'
    have hform : g * c * g⁻¹ = ⁅g, c⁆ * c := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    refine (Bright T i Vi).mul_mem
      ((le_sup_right : Kright T i ≤ Vi ⊔ Kright T i) hcomm) ?_
    exact (le_sup_right : Kright T i ≤ Vi ⊔ Kright T i)
      ((le_iSup₂_of_le (n - i) ⟨by omega, by omega⟩ le_rfl : T.U (n - i) ≤ Kright T i) hc')
  rw [Vsub, Subgroup.map_sup, Subgroup.map_sup]
  exact sup_le (sup_le hViMap hWMap) hVniMap

private theorem Vsub_map_mu_zero_le (hn : 3 ≤ n) {i : ℤ} {Vi Vni : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i))
    (hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      Vi.map (MulAut.conj (T.mu 0 u)).toMonoidHom = Vni)
    {v : G} (hv : v ∈ T.U 0) (hv1 : v ≠ 1) :
    (Vsub T i Vi Vni).map (MulAut.conj (T.mu 0 v)).toMonoidHom ≤ Vsub T i Vi Vni := by
  set m := T.mu 0 v
  have hmoves : T.Moves m (fun j => (n : ℤ) - j) := by
    simpa [m] using T.moves_mu hv hv1
  have hW : (Wmid T i).map (MulAut.conj m).toMonoidHom = Wmid T i := by
    have h := Moves.map_win_refl T hmoves (i + 1) (n - i - 1)
    simp only [Wmid]
    rw [h, show n - (n - i - 1) = i + 1 by omega,
      show n - (i + 1) = n - i - 1 by omega]
  have hViMap : Vi.map (MulAut.conj m).toMonoidHom = Vni := by
    simpa [m] using hconj v hv hv1
  have hVniMap : Vni.map (MulAut.conj m).toMonoidHom = Vi := by
    have hv' : v⁻¹ ∈ T.U 0 := (T.U 0).inv_mem hv
    have hv1' : v⁻¹ ≠ 1 := inv_ne_one.mpr hv1
    have h := hconj v⁻¹ hv' hv1'
    rw [T.mu_inv hn hv hv1] at h
    have := CFSG.LieType.Steinberg.map_conj_inv_of_map_conj h
    simpa [m] using this
  rw [Vsub, Subgroup.map_sup, Subgroup.map_sup, hViMap, hW, hVniMap]
  exact le_of_eq (by ac_rfl)

private theorem map_conj_le_Vsub_of_mem_Un (hn : 3 ≤ n) {i : ℤ} {Vi Vni Y : Subgroup G}
    (hi : 0 < i) (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i))
    (hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      Vi.map (MulAut.conj (T.mu 0 u)).toMonoidHom = Vni)
    (hY : Y ≤ Vsub T i Vi Vni) (hY0 : T.U 0 ≤ Subgroup.normalizer (Y : Set G))
    {u : G} (hu : u ∈ T.U n) (hu1 : u ≠ 1) :
    Y.map (MulAut.conj u).toMonoidHom ≤ Vsub T i Vi Vni := by
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun y hy => ?_
  have hnu : T.nu n u ∈ T.U 0 := by
    have h : T.nu n u ∈ T.U ((n : ℤ) + n) := (T.isMu_nu hu hu1).1
    rwa [show (n : ℤ) + n = (0 : ℤ) + 2 * (n : ℤ) by ring, T.periodic] at h
  have hnu1 : T.nu n u ≠ 1 := T.nu_ne_one hn hu hu1
  have hnu_inv : (T.nu n u)⁻¹ ∈ T.U 0 := (T.U 0).inv_mem hnu
  have hnu' : T.nu' n u ∈ T.U 0 := by
    have h : T.nu' n u ∈ T.U ((n : ℤ) + n) := (T.isMu_nu hu hu1).2.1
    rwa [show (n : ℤ) + n = (0 : ℤ) + 2 * (n : ℤ) by ring, T.periodic] at h
  have hzY : (T.nu' n u)⁻¹ * y * T.nu' n u ∈ Y := by
    have hnorm := hY0 ((T.U 0).inv_mem hnu')
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy
  have hmV : T.mu n u * ((T.nu' n u)⁻¹ * y * T.nu' n u) * (T.mu n u)⁻¹ ∈
      Vsub T i Vi Vni := by
    have hpres := Vsub_map_mu_zero_le T hn hi hi2 hVi hVni hconj hnu hnu1
    rw [← mu_n_eq_mu_zero_nu T hn hu hu1] at hpres
    exact hpres ⟨_, hY hzY, rfl⟩
  have hdecomp : u = (T.nu n u)⁻¹ * T.mu n u * (T.nu' n u)⁻¹ := by
    simp only [mu]
    group
  have heq : u * y * u⁻¹ =
      (T.nu n u)⁻¹ * (T.mu n u * ((T.nu' n u)⁻¹ * y * T.nu' n u) *
        (T.mu n u)⁻¹) * T.nu n u := by
    conv_lhs => rw [hdecomp]
    group
  have hA : u * y * u⁻¹ ∈ Aleft T i Vni := by
    rw [heq]
    exact (Vsub_map_conj_le_Aleft T hi hi2 hVi hVni hnu_inv) ⟨_, hmV, by simp⟩
  have hB : u * y * u⁻¹ ∈ Bright T i Vi :=
    (Vsub_map_conj_le_Bright T hi hi2 hVi hVni hu) ⟨y, hY hy, rfl⟩
  rw [← Aleft_inf_Bright_eq_Vsub T hi hi2 hVi hVni]
  exact ⟨hA, hB⟩

private theorem map_conj_le_Vsub_of_mem_U0 (hn : 3 ≤ n) {i : ℤ} {Vi Vni Y : Subgroup G}
    (hi : 0 < i) (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i))
    (hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      Vi.map (MulAut.conj (T.mu 0 u)).toMonoidHom = Vni)
    (hY : Y ≤ Vsub T i Vi Vni) (hYn : T.U n ≤ Subgroup.normalizer (Y : Set G))
    {u : G} (hu : u ∈ T.U 0) (hu1 : u ≠ 1) :
    Y.map (MulAut.conj u).toMonoidHom ≤ Vsub T i Vi Vni := by
  refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun y hy => ?_
  have hnu : T.nu 0 u ∈ T.U n := by
    simpa using (T.isMu_nu (i := 0) hu hu1).1
  have hnu_inv : (T.nu 0 u)⁻¹ ∈ T.U n := (T.U n).inv_mem hnu
  have hnu' : T.nu' 0 u ∈ T.U n := by
    simpa using (T.isMu_nu (i := 0) hu hu1).2.1
  have hzY : (T.nu' 0 u)⁻¹ * y * T.nu' 0 u ∈ Y := by
    have hnorm := hYn ((T.U n).inv_mem hnu')
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy
  have hmV : T.mu 0 u * ((T.nu' 0 u)⁻¹ * y * T.nu' 0 u) * (T.mu 0 u)⁻¹ ∈
      Vsub T i Vi Vni :=
    (Vsub_map_mu_zero_le T hn hi hi2 hVi hVni hconj hu hu1) ⟨_, hY hzY, rfl⟩
  have hdecomp : u = (T.nu 0 u)⁻¹ * T.mu 0 u * (T.nu' 0 u)⁻¹ := by
    simp only [mu]
    group
  have heq : u * y * u⁻¹ =
      (T.nu 0 u)⁻¹ * (T.mu 0 u * ((T.nu' 0 u)⁻¹ * y * T.nu' 0 u) *
        (T.mu 0 u)⁻¹) * T.nu 0 u := by
    conv_lhs => rw [hdecomp]
    group
  have hA : u * y * u⁻¹ ∈ Aleft T i Vni :=
    (Vsub_map_conj_le_Aleft T hi hi2 hVi hVni hu) ⟨y, hY hy, rfl⟩
  have hB : u * y * u⁻¹ ∈ Bright T i Vi := by
    rw [heq]
    exact (Vsub_map_conj_le_Bright T hi hi2 hVi hVni hnu_inv) ⟨_, hmV, by simp⟩
  rw [← Aleft_inf_Bright_eq_Vsub T hi hi2 hVi hVni]
  exact ⟨hA, hB⟩

private def conjClosure (A Y : Subgroup G) : Subgroup G :=
  ⨆ a ∈ A, Y.map (MulAut.conj a).toMonoidHom

private theorem le_conjClosure (A Y : Subgroup G) : Y ≤ conjClosure A Y := by
  have h : Y.map (MulAut.conj (1 : G)).toMonoidHom ≤ conjClosure A Y :=
    le_iSup₂_of_le 1 A.one_mem le_rfl
  rwa [CFSG.LieType.Steinberg.map_conj_one] at h

private theorem conjClosure_le {A Y Z : Subgroup G} (h : ∀ a ∈ A,
    Y.map (MulAut.conj a).toMonoidHom ≤ Z) : conjClosure A Y ≤ Z :=
  iSup₂_le h

private theorem conjClosure_normalized (A Y : Subgroup G) :
    A ≤ Subgroup.normalizer (conjClosure A Y : Set G) := by
  refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun a ha => ?_
  simp only [conjClosure, Subgroup.map_iSup]
  refine iSup₂_le fun b hb => ?_
  rw [← CFSG.LieType.Steinberg.map_conj_mul a b Y]
  exact le_iSup₂_of_le (a * b) (A.mul_mem ha hb) le_rfl

private noncomputable def chainP (X : Subgroup G) : ℕ → Subgroup G
  | 0 => X
  | k + 1 => conjClosure (T.U 0) (conjClosure (T.U n) (chainP X k))

private noncomputable def chainQ (X : Subgroup G) (k : ℕ) : Subgroup G :=
  conjClosure (T.U n) (chainP T X k)

private theorem chainP_zero (X : Subgroup G) : chainP T X 0 = X := rfl

private theorem chainP_succ (X : Subgroup G) (k : ℕ) :
    chainP T X (k + 1) = conjClosure (T.U 0) (chainQ T X k) := rfl

private theorem chainQ_le_chainP_succ (X : Subgroup G) (k : ℕ) :
    chainQ T X k ≤ chainP T X (k + 1) := by
  rw [chainP_succ]
  exact le_conjClosure (T.U 0) (chainQ T X k)

private theorem chainP_normalized_U0 {X : Subgroup G}
    (hX0 : T.U 0 ≤ Subgroup.normalizer (X : Set G)) (k : ℕ) :
    T.U 0 ≤ Subgroup.normalizer (chainP T X k : Set G) := by
  induction k with
  | zero => rw [chainP_zero]; exact hX0
  | succ k ih =>
      rw [chainP_succ]
      exact conjClosure_normalized (T.U 0) (chainQ T X k)

private theorem chainQ_normalized_Un (X : Subgroup G) (k : ℕ) :
    T.U n ≤ Subgroup.normalizer (chainQ T X k : Set G) :=
  conjClosure_normalized (T.U n) (chainP T X k)

private theorem chainQ_le_Vsub (hn : 3 ≤ n) {i : ℤ} {Vi Vni X : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i))
    (hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      Vi.map (MulAut.conj (T.mu 0 u)).toMonoidHom = Vni)
    (hX0 : T.U 0 ≤ Subgroup.normalizer (X : Set G)) {k : ℕ}
    (hP : chainP T X k ≤ Vsub T i Vi Vni) : chainQ T X k ≤ Vsub T i Vi Vni := by
  rw [chainQ]
  refine conjClosure_le fun u hu => ?_
  by_cases hu1 : u = 1
  · subst hu1
    rw [CFSG.LieType.Steinberg.map_conj_one]
    exact hP
  · exact map_conj_le_Vsub_of_mem_Un T hn hi hi2 hVi hVni hconj hP
      (chainP_normalized_U0 T hX0 k) hu hu1

private theorem chainP_le_Vsub (hn : 3 ≤ n) {i : ℤ} {Vi Vni X : Subgroup G} (hi : 0 < i)
    (hi2 : 2 * i < n) (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i))
    (hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      Vi.map (MulAut.conj (T.mu 0 u)).toMonoidHom = Vni)
    (hX0 : T.U 0 ≤ Subgroup.normalizer (X : Set G))
    (hXV : X ≤ Vsub T i Vi Vni) (k : ℕ) : chainP T X k ≤ Vsub T i Vi Vni := by
  induction k with
  | zero => rw [chainP_zero]; exact hXV
  | succ k ih =>
      rw [chainP_succ]
      refine conjClosure_le fun u hu => ?_
      by_cases hu1 : u = 1
      · subst hu1
        rw [CFSG.LieType.Steinberg.map_conj_one]
        exact chainQ_le_Vsub T hn hi hi2 hVi hVni hconj hX0 ih
      · exact map_conj_le_Vsub_of_mem_U0 T hn hi hi2 hVi hVni hconj
          (chainQ_le_Vsub T hn hi hi2 hVi hVni hconj hX0 ih)
          (chainQ_normalized_Un T X k) hu hu1

theorem lemma214 (hn : 3 ≤ n) {i : ℤ} (hi : 0 < i) (hi2 : 2 * i < n) (Vi Vni X : Subgroup G)
    (hVi : Vi ≤ T.U i) (hVni : Vni ≤ T.U (n - i))
    (hconj : ∀ u ∈ T.U 0, u ≠ 1 →
      Vi.map (MulAut.conj (T.mu 0 u)).toMonoidHom = Vni)
    (hX : (X : Set G) ⊆ (Vi : Set G) * (win T.U (i + 1) (n - i - 1) : Set G) * (Vni : Set G))
    (hX0 : T.U 0 ≤ Subgroup.normalizer (X : Set G)) :
    ((normClosure2 (T.U 0) (T.U n) X : Subgroup G) : Set G) ⊆
      (Vi : Set G) * (win T.U (i + 1) (n - i - 1) : Set G) * (Vni : Set G) := by
  have hXV : X ≤ Vsub T i Vi Vni := by
    change (X : Set G) ⊆ (Vsub T i Vi Vni : Set G)
    rw [coe_Vsub T hi hi2 hVi hVni]
    exact hX
  let Y : Subgroup G := ⨆ k, chainP T X k
  have hPle : ∀ k, chainP T X k ≤ Vsub T i Vi Vni :=
    chainP_le_Vsub T hn hi hi2 hVi hVni hconj hX0 hXV
  have hYle : Y ≤ Vsub T i Vi Vni := iSup_le hPle
  have hXY : X ≤ Y := by
    have h := le_iSup (fun k => chainP T X k) 0
    rwa [chainP_zero] at h
  have hY0 : T.U 0 ≤ Subgroup.normalizer (Y : Set G) := by
    exact CFSG.LieType.Steinberg.le_normalizer_iSup
      (A := T.U 0) (B := fun k => chainP T X k)
      (fun k => chainP_normalized_U0 T hX0 k)
  have hYn : T.U n ≤ Subgroup.normalizer (Y : Set G) := by
    refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun u hu => ?_
    have hmap : Y.map (MulAut.conj u).toMonoidHom =
        ⨆ k, (chainP T X k).map (MulAut.conj u).toMonoidHom := by
      dsimp [Y]
      rw [Subgroup.map_iSup]
    rw [hmap]
    refine iSup_le fun k => ?_
    have h1 : (chainP T X k).map (MulAut.conj u).toMonoidHom ≤ chainQ T X k :=
      le_iSup₂_of_le u hu le_rfl
    exact h1.trans ((chainQ_le_chainP_succ T X k).trans
      (le_iSup (fun k => chainP T X k) (k + 1)))
  have hNorm : normClosure2 (T.U 0) (T.U n) X ≤ Y := by
    rw [normClosure2]
    exact sInf_le ⟨hXY, hY0, hYn⟩
  intro x hx
  have hxV : x ∈ (Vsub T i Vi Vni : Set G) := hYle (hNorm hx)
  rw [coe_Vsub T hi hi2 hVi hVni] at hxV
  simpa [Wmid] using hxV

end TitsSystem

end CFSG.GH74.Tits83
