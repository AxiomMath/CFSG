module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameFixed
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.M12ListB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup CFSG.Blueprint

variable {K : Type} [Group K]

structure AlphaData (x₁ x₂ lam rho : K) (α : MulAut K) : Prop where
  sq : α * α = 1
  outer : ∀ k : K, α ≠ MulAut.conj k
  x₁ : α x₁ = x₁⁻¹
  x₂ : α x₂ = x₂⁻¹
  lam : α lam = lam
  rho : α rho = rho

theorem map_fourGrp_sup_zpowers' {G H : Type*} [Group G] [Group H] (f : G →* H)
    (x₁ x₂ lam : G) :
    (fourGrp x₁ x₂ ⊔ zpowers lam).map f = fourGrp (f x₁) (f x₂) ⊔ zpowers (f lam) := by
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  congr 1
  rw [show fourGrp x₁ x₂ = Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set G) from rfl,
    show fourGrp (f x₁) (f x₂) =
      Subgroup.closure ({f x₁ ^ 2, (f x₁ * f x₂) ^ 2} : Set H) from rfl,
    MonoidHom.map_closure]
  congr 1
  simp only [Set.image_pair, map_pow, map_mul]

theorem closure_yzl_eq (x₁ x₂ lam : K) :
    Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set K) = fourGrp x₁ x₂ ⊔ zpowers lam := by
  rw [show fourGrp x₁ x₂ = Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2} : Set K) from rfl,
    Subgroup.zpowers_eq_closure lam, ← Subgroup.closure_union]
  congr 1
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem map_wreathGrp' {G H : Type*} [Group G] [Group H] (f : G →* H) (x₁ x₂ lam : G) :
    (wreathGrp x₁ x₂ lam).map f = wreathGrp (f x₁) (f x₂) (f lam) := by
  rw [show wreathGrp x₁ x₂ lam = Subgroup.closure ({x₁, x₂, lam} : Set G) from rfl,
    show wreathGrp (f x₁) (f x₂) (f lam) =
      Subgroup.closure ({f x₁, f x₂, f lam} : Set H) from rfl,
    MonoidHom.map_closure]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rcases hw with rfl | rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨x₁, by simp, rfl⟩
    · exact ⟨x₂, by simp, rfl⟩
    · exact ⟨lam, by simp, rfl⟩

section Cert


theorem exists_adapted_frame (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam : K}
    (hw : WreathRel x₁ x₂ lam) (Ŝ : Subgroup (MulAut K)) (hcard : Nat.card Ŝ = 64)
    (hŜT : ∀ w : K, MulAut.conj w ∈ Ŝ → w ∈ wreathGrp x₁ x₂ lam) :
    ∃ (x₁' x₂' lam' rho' : K) (α' : MulAut K), U33Frame x₁' x₂' lam' rho' α' ∧
      U33FrameExtras x₁' x₂' lam' rho' α' ∧ baseGrp x₁' x₂' = baseGrp x₁ x₂ ∧ α' ∈ Ŝ := by
  haveI hFinAut : Finite (MulAut K) :=
    Nat.finite_of_card_ne_zero (by rw [card_aut_of_psu33 hK]; norm_num)
  have hfac : (12096 : ℕ).factorization 2 = 6 := by
    have h12096 : (12096 : ℕ) = 2 ^ 6 * 189 := by norm_num
    rw [h12096, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have hfacM : (Nat.card (MulAut K)).factorization 2 = 6 := by
    rw [card_aut_of_psu33 hK, show 2 * 6048 = 12096 from by norm_num]
    exact hfac
  have hcard' : Nat.card Ŝ = 2 ^ (Nat.card (MulAut K)).factorization 2 := by
    rw [hcard, hfacM]
    norm_num
  let Ssyl : Sylow 2 (MulAut K) := Sylow.ofCard Ŝ hcard'
  have hcoe : (Ssyl : Subgroup (MulAut K)) = Ŝ := Sylow.coe_ofCard Ŝ hcard'
  obtain ⟨x₁', x₂', lam', rho', α', hf, he, hS⟩ := exists_frame_extras_of_sylow hK Ssyl
  rw [hcoe] at hS
  have hgen : ∀ g ∈ ({MulAut.conj x₁', MulAut.conj x₂', MulAut.conj lam', α'} :
      Set (MulAut K)), g ∈ Ŝ := by
    intro g hg
    rw [← hS]
    exact Subgroup.subset_closure hg
  have hx₁'T : x₁' ∈ wreathGrp x₁ x₂ lam := hŜT x₁' (hgen _ (by simp))
  have hx₂'T : x₂' ∈ wreathGrp x₁ x₂ lam := hŜT x₂' (hgen _ (by simp))
  have hB'T : baseGrp x₁' x₂' ≤ wreathGrp x₁ x₂ lam := by
    refine (Subgroup.closure_le (K := wreathGrp x₁ x₂ lam)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact hx₁'T
    · rw [hg]
      exact hx₂'T
  obtain ⟨hAb, -, hcardB⟩ := hf.wreath.baseGrp_eq
  exact ⟨x₁', x₂', lam', rho', α', hf, he,
    hw.eq_baseGrp_of_card_sixteen hB'T hAb hcardB, hgen α' (by simp)⟩

theorem exists_alpha (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K}
    (hw : WreathRel x₁ x₂ lam)
    (hρN : ∀ w ∈ baseGrp x₁ x₂, rho * w * rho⁻¹ ∈ baseGrp x₁ x₂)
    (hρC : ∀ w ∈ baseGrp x₁ x₂, rho * w = w * rho → w = 1)
    (hlr : lam * rho * lam⁻¹ = rho⁻¹) (Ŝ : Subgroup (MulAut K)) (hcard : Nat.card Ŝ = 64)
    (hTŜ : ∀ w ∈ wreathGrp x₁ x₂ lam, MulAut.conj w ∈ Ŝ)
    (hŜT : ∀ w : K, MulAut.conj w ∈ Ŝ → w ∈ wreathGrp x₁ x₂ lam) :
    ∃ α ∈ Ŝ, AlphaData x₁ x₂ lam rho α := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [card_K_of_psu33 hK]; norm_num)
  obtain ⟨x₁', x₂', lam', rho', α', hf, he, hBB, hα'Ŝ⟩ := exists_adapted_frame hK hw Ŝ hcard hŜT
  have hx₁B : x₁ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hx₂B : x₂ ∈ baseGrp x₁ x₂ := Subgroup.subset_closure (by simp)
  have hBT : baseGrp x₁ x₂ ≤ wreathGrp x₁ x₂ lam := by
    refine (Subgroup.closure_le (K := wreathGrp x₁ x₂ lam)).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
  have hinvB : ∀ w ∈ baseGrp x₁ x₂, α' w = w⁻¹ := by
    intro w hw'
    refine alpha_inv_of_mem_baseGrp hf.wreath hf.alpha_x₁ hf.alpha_x₂ ?_
    rw [hBB]
    exact hw'
  have hF2 : ∀ n : K, (∀ w ∈ baseGrp x₁ x₂, n * w * n⁻¹ ∈ baseGrp x₁ x₂) →
      n⁻¹ * α' n ∈ baseGrp x₁ x₂ := by
    intro n hn
    rw [← hBB] at hn ⊢
    exact tau_acts_trivially hf he hn
  obtain ⟨c, hcB, hc⟩ := exists_adjust hρN hρC (hF2 rho hρN)
  have hαapp : ∀ z : K, (MulAut.conj c * α') z = c * α' z * c⁻¹ := fun z => by
    rw [MulAut.mul_apply, MulAut.conj_apply]
  have hαB : ∀ w ∈ baseGrp x₁ x₂, (MulAut.conj c * α') w = w⁻¹ := by
    intro w hw'
    rw [hαapp, hinvB w hw']
    have hcom : c * w⁻¹ = w⁻¹ * c := baseGrp_comm hw hcB (Subgroup.inv_mem _ hw')
    calc c * w⁻¹ * c⁻¹ = (w⁻¹ * c) * c⁻¹ := by rw [hcom]
      _ = w⁻¹ := by group
  have hαρ : (MulAut.conj c * α') rho = rho := by
    rw [hαapp]
    have e1 : α' rho = rho * ((rho⁻¹ * c * rho)⁻¹ * c) := by
      rw [hc]
      group
    rw [e1]
    group
  have hlamN : ∀ w ∈ baseGrp x₁ x₂, lam * w * lam⁻¹ ∈ baseGrp x₁ x₂ :=
    conj_mem_baseGrp_of_gens (by rw [hw.conj_x₁]; exact hx₂B)
      (by rw [wr_lam_conj_x₂ hw]; exact hx₁B)
  have hlaminv : lam⁻¹ = lam := inv_eq_of_mul_eq_one_right (wr_lam_sq hw)
  have hlamN' : lam⁻¹ * c * lam ∈ baseGrp x₁ x₂ := by
    have := hlamN c hcB
    rwa [hlaminv] at this ⊢
  have hbl := hF2 lam hlamN
  obtain ⟨b, hbB, hb⟩ : ∃ b ∈ baseGrp x₁ x₂, (MulAut.conj c * α') lam = lam * b := by
    refine ⟨(lam⁻¹ * c * lam) * (lam⁻¹ * α' lam) * c⁻¹,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hlamN' hbl) (Subgroup.inv_mem _ hcB), ?_⟩
    rw [hαapp]
    group
  have hrel : (MulAut.conj c * α') lam * rho * ((MulAut.conj c * α') lam)⁻¹ = rho⁻¹ := by
    have := congrArg (fun x => (MulAut.conj c * α') x) hlr
    simpa only [map_mul, map_inv, hαρ] using this
  rw [hb] at hrel
  have hbρ : b * rho = rho * b := by
    have h1 : lam * (b * rho * b⁻¹) * lam⁻¹ = lam * rho * lam⁻¹ := by
      calc lam * (b * rho * b⁻¹) * lam⁻¹ = (lam * b) * rho * (lam * b)⁻¹ := by group
        _ = rho⁻¹ := hrel
        _ = lam * rho * lam⁻¹ := hlr.symm
    have h2 : b * rho * b⁻¹ = rho := mul_left_cancel (mul_right_cancel h1)
    calc b * rho = (b * rho * b⁻¹) * b := by group
      _ = rho * b := by rw [h2]
  have hb1 : b = 1 := hρC b hbB hbρ.symm
  refine ⟨MulAut.conj c * α', Subgroup.mul_mem _ (hTŜ c (hBT hcB)) hα'Ŝ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext z
    have hα'z : α' (α' z) = z := by
      have := congrArg (fun f : MulAut K => f z) hf.alpha_sq
      simpa using this
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply, map_mul, map_inv, hα'z,
      hinvB c hcB, inv_inv]
    group
  · intro k hk
    apply hf.alpha_outer (c⁻¹ * k)
    have h1 : α' = (MulAut.conj c)⁻¹ * MulAut.conj k := by
      rw [← hk]
      group
    rw [h1, map_mul, map_inv]
  · exact hαB x₁ hx₁B
  · exact hαB x₂ hx₂B
  · rw [hb, hb1, mul_one]
  · exact hαρ

theorem AlphaData.m12 (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K} {α : MulAut K}
    (hw : WreathRel x₁ x₂ lam) (hα : AlphaData x₁ x₂ lam rho α) :
    M12Rel (MulAut.conj x₁) (MulAut.conj x₂) (MulAut.conj lam) α := by
  have hα1 : α ≠ 1 := fun h1 =>
    hα.outer 1 (h1.trans (map_one (MulAut.conj : K →* MulAut K)).symm)
  have hα2 : α ^ 2 = 1 := by
    rw [pow_two]
    exact hα.sq
  refine
    { toWreathRel := WreathRel.map' (MulAut.conj : K →* MulAut K)
        (conj_injective_of_psu33 hK) hw
      ord_tau := orderOf_eq_prime hα2 hα1
      comm_lam_tau := ?_
      tau_x₁ := ?_
      tau_x₂ := ?_ }
  · have h2 : α * MulAut.conj lam * α⁻¹ = MulAut.conj lam := by
      rw [aut_mul_conj_mul_inv, hα.lam]
    calc MulAut.conj lam * α = (α * MulAut.conj lam * α⁻¹) * α := by
          conv_lhs => rw [← h2]
      _ = α * MulAut.conj lam := by group
  · calc α * MulAut.conj x₁ * α⁻¹ = MulAut.conj (α x₁) := aut_mul_conj_mul_inv α x₁
      _ = MulAut.conj x₁⁻¹ := by rw [hα.x₁]
      _ = (MulAut.conj x₁)⁻¹ := map_inv (MulAut.conj : K →* MulAut K) x₁
  · calc α * MulAut.conj x₂ * α⁻¹ = MulAut.conj (α x₂) := aut_mul_conj_mul_inv α x₂
      _ = MulAut.conj x₂⁻¹ := by rw [hα.x₂]
      _ = (MulAut.conj x₂)⁻¹ := map_inv (MulAut.conj : K →* MulAut K) x₂

theorem AlphaData.card_fourGrp_sup_zpowers (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K}
    {α : MulAut K} (hw : WreathRel x₁ x₂ lam) (hα : AlphaData x₁ x₂ lam rho α) :
    Nat.card (fourGrp x₁ x₂ ⊔ zpowers lam : Subgroup K) = 8 := by
  obtain ⟨e⟩ := (M12Rel.centralizer_tau (hα.m12 hK hw)).2.2
  rw [← Subgroup.card_map_of_injective (K := fourGrp x₁ x₂ ⊔ zpowers lam)
    (f := (MulAut.conj : K →* MulAut K)) (conj_injective_of_psu33 hK),
    map_fourGrp_sup_zpowers' (MulAut.conj : K →* MulAut K) x₁ x₂ lam, Nat.card_congr e.toEquiv,
    DihedralGroup.nat_card]

theorem AlphaData.autFixed_eq (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K} {α : MulAut K}
    (hw : WreathRel x₁ x₂ lam) (hρ : orderOf rho = 3) (hα : AlphaData x₁ x₂ lam rho α) :
    autFixed α = Subgroup.closure {x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} := by
  let M := Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Set K)
  have h4a : x₁ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₁
    rwa [hw.ord_x₁] at this
  have h4b : x₂ ^ 4 = 1 := by
    have := pow_orderOf_eq_one x₂
    rwa [hw.ord_x₂] at this
  have hcomm : Commute x₁ x₂ := hw.comm
  have hsub : M ≤ autFixed α := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with hg | hg | hg | hg
    · rw [hg]
      change α (x₁ ^ 2) = x₁ ^ 2
      rw [map_pow, hα.x₁, inv_pow, inv_eq_iff_mul_eq_one,
        ← pow_add, show (2 : ℕ) + 2 = 4 from rfl, h4a]
    · rw [hg]
      change α ((x₁ * x₂) ^ 2) = (x₁ * x₂) ^ 2
      rw [map_pow, map_mul, hα.x₁, hα.x₂]
      have h4c : (x₁ * x₂) ^ 4 = 1 := by rw [hcomm.mul_pow, h4a, h4b, mul_one]
      have hinv : x₁⁻¹ * x₂⁻¹ = (x₁ * x₂)⁻¹ := by
        rw [mul_inv_rev]
        exact (hcomm.inv_inv).eq
      rw [hinv, inv_pow, inv_eq_iff_mul_eq_one, ← pow_add,
        show (2 : ℕ) + 2 = 4 from rfl, h4c]
    · rw [hg]
      change α rho = rho
      exact hα.rho
    · rw [hg]
      change α lam = lam
      exact hα.lam
  have hcard24 : Nat.card (autFixed α) = 24 := autFixed_card_of_psu33 hK hα.sq hα.outer
  haveI : Finite (autFixed α) := Nat.finite_of_card_ne_zero (by rw [hcard24]; norm_num)
  have hDle : Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set K) ≤ M := by
    apply Subgroup.closure_mono
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hcardD : Nat.card (Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set K)) = 8 := by
    rw [closure_yzl_eq]
    exact hα.card_fourGrp_sup_zpowers hK hw
  have h3 : 3 ∣ Nat.card M := by
    have hmem : rho ∈ M := Subgroup.subset_closure (by simp)
    rw [← hρ]
    exact Subgroup.orderOf_dvd_natCard M hmem
  have h8 : 8 ∣ Nat.card M := by
    rw [← hcardD]
    exact Subgroup.card_dvd_of_le hDle
  have h24 : 24 ∣ Nat.card M := by
    rw [show (24 : ℕ) = 8 * 3 from rfl]
    exact (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h8 h3)
  haveI : Nonempty M := ⟨⟨1, M.one_mem⟩⟩
  haveI : Finite M :=
    Finite.of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)
  have hcardM : Nat.card M = 24 := by
    have hle : Nat.card M ≤ 24 := by
      rw [← hcard24]
      exact Subgroup.card_le_of_le hsub
    exact Nat.le_antisymm hle (Nat.le_of_dvd Nat.card_pos h24)
  exact (Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard24, hcardM])).symm

theorem AlphaData.wreathGrp_inf_autFixed (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K}
    {α : MulAut K} (hw : WreathRel x₁ x₂ lam) (hα : AlphaData x₁ x₂ lam rho α) :
    wreathGrp x₁ x₂ lam ⊓ autFixed α = Subgroup.closure {x₁ ^ 2, (x₁ * x₂) ^ 2, lam} := by
  let f : K →* MulAut K := MulAut.conj
  have hinj : Function.Injective f := conj_injective_of_psu33 hK
  have hm12 : M12Rel (f x₁) (f x₂) (f lam) α := hα.m12 hK hw
  have hmap_wreath : (wreathGrp x₁ x₂ lam).map f = wreathGrp (f x₁) (f x₂) (f lam) :=
    map_wreathGrp' f x₁ x₂ lam
  have hmap_four : (fourGrp x₁ x₂ ⊔ zpowers lam).map f
      = fourGrp (f x₁) (f x₂) ⊔ zpowers (f lam) := map_fourGrp_sup_zpowers' f x₁ x₂ lam
  have hmap_aut : (autFixed α).map f
      = f.range ⊓ Subgroup.centralizer ({α} : Set (MulAut K)) := by
    apply le_antisymm
    · rintro z ⟨k, hk, rfl⟩
      refine ⟨⟨k, rfl⟩, ?_⟩
      change ∀ y ∈ ({α} : Set (MulAut K)), y * f k = f k * y
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have hk' : α k = k := hk
      have hconj : α * f k * α⁻¹ = f k := by
        rw [show α * f k * α⁻¹ = MulAut.conj (α k) from aut_mul_conj_mul_inv α k, hk']
      calc α * f k = (α * f k * α⁻¹) * α := by group
        _ = f k * α := by rw [hconj]
    · rintro z ⟨⟨k, rfl⟩, hz⟩
      refine ⟨k, ?_, rfl⟩
      change α k = k
      have hz' : α * f k = f k * α := by
        change ∀ y ∈ ({α} : Set (MulAut K)), y * f k = f k * y at hz
        exact hz α (by simp)
      have hconj : MulAut.conj (α k) = MulAut.conj k := by
        have hz'' : α * MulAut.conj k = MulAut.conj k * α := hz'
        rw [← aut_mul_conj_mul_inv α k, hz'']
        group
      exact hinj hconj
  have hmapinj : Function.Injective (Subgroup.map f) := fun A B hAB => by
    rw [← Subgroup.comap_map_eq_self_of_injective hinj A, hAB,
      Subgroup.comap_map_eq_self_of_injective hinj B]
  apply hmapinj
  rw [Subgroup.map_inf (wreathGrp x₁ x₂ lam) (autFixed α) f hinj, hmap_wreath, hmap_aut,
    closure_yzl_eq, hmap_four]
  have hwreath_le : wreathGrp (f x₁) (f x₂) (f lam) ≤ f.range := by
    rw [← hmap_wreath]
    exact Subgroup.map_le_range f _
  rw [← inf_assoc, inf_eq_left.mpr hwreath_le]
  exact M12Rel.centralizer_tau_inf_wreathGrp hm12

theorem AlphaData.perm_four (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K} {α : MulAut K}
    (hα : AlphaData x₁ x₂ lam rho α) : Nonempty (↥(autFixed α) ≃* Equiv.Perm (Fin 4)) :=
  autFixed_perm_four_of_psu33 hK hα.sq hα.outer

theorem AlphaData.dihedral (hK : LieModel K .PSU 3 3 1) {x₁ x₂ lam rho : K} {α : MulAut K}
    (hw : WreathRel x₁ x₂ lam) (hα : AlphaData x₁ x₂ lam rho α) :
    Nonempty (↥(Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set K)) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := (M12Rel.centralizer_tau (hα.m12 hK hw)).2.2
  have hinj : Function.Injective (MulAut.conj : K →* MulAut K) := conj_injective_of_psu33 hK
  have hmap : (Subgroup.closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set K)).map
        (MulAut.conj : K →* MulAut K) =
      fourGrp (MulAut.conj x₁) (MulAut.conj x₂) ⊔ zpowers (MulAut.conj lam) := by
    rw [closure_yzl_eq, map_fourGrp_sup_zpowers']
  exact ⟨((Subgroup.equivMapOfInjective _ (MulAut.conj : K →* MulAut K) hinj).trans
    (MulEquiv.subgroupCongr hmap)).trans e⟩

end Cert

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
