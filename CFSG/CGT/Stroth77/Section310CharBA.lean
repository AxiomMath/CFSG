module

public import CFSG.CGT.Stroth77.Section310CharB
public import CFSG.CGT.Stroth77.Section43CoreE

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem StrothFrame.IsD.exists_d8_inv_mul_mem (h : F.IsD D dD) (hk : ∀ i, 1 ≤ τ.k i)
    (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w) {n : G}
    (hn : n ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G)) :
    ∃ i j l : Bool, ∀ w ∈ omegaIn 1 D,
      w * ((dD.d8 i j l)⁻¹ * n) = (dD.d8 i j l)⁻¹ * n * w := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  set Ω : Subgroup G := omegaIn 1 D with hΩ
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hDN : D ≤ N := le_inf h.le_S Subgroup.le_normalizer
  have hΩN : Ω ≤ N := (omegaIn_le 1 D).trans hDN
  have huvN : dD.uv ∈ N := ⟨h.uv_eq ▸ F.uv_mem_S, dD.uv_mem⟩
  have htN : dD.t ∈ N := ⟨h.t_eq ▸ F.t_mem_S, dD.t_mem⟩
  have huN : dD.u ∈ N := ⟨h.u_eq ▸ F.u_mem_S, dD.u_mem⟩
  have htu : dD.t⁻¹ * dD.u⁻¹ * dD.t * dD.u = dD.uv := by
    have ht' : dD.t⁻¹ = dD.t := inv_eq_of_mul_eq_one_right dD.t_sq
    have hu' : dD.u⁻¹ = dD.u := inv_eq_of_mul_eq_one_right dD.u_sq
    calc dD.t⁻¹ * dD.u⁻¹ * dD.t * dD.u = dD.t * (dD.u * (dD.t * dD.u)) := by
          rw [ht', hu']; group
      _ = dD.t * (dD.u * dD.u) * dD.uv * dD.t := by rw [dD.t_u]; group
      _ = dD.t * dD.uv * dD.t := by rw [dD.u_sq, mul_one]
      _ = dD.uv * (dD.t * dD.t) := by rw [← dD.uv_comm_t]; group
      _ = dD.uv := by rw [dD.t_sq, mul_one]
  have hΩnorm : ∀ x ∈ N, ∀ w ∈ Ω, x * w * x⁻¹ ∈ Ω := by
    intro x hx w hw
    obtain ⟨hwD, hw2⟩ := (mem_omegaIn_one_iff hDc).mp hw
    refine mem_omegaIn_one_of_mul_self ((Subgroup.mem_normalizer_iff.mp hx.2 w).mp hwD) ?_
    calc x * w * x⁻¹ * (x * w * x⁻¹) = x * (w * w) * x⁻¹ := by group
      _ = 1 := by rw [hw2, mul_one, mul_inv_cancel]
  haveI : (Ω.subgroupOf N).Normal := ⟨fun w hw x => Subgroup.mem_subgroupOf.mpr (by
    simpa using hΩnorm x x.2 w (Subgroup.mem_subgroupOf.mp hw))⟩
  let θ : ↥N →* MulAut ↥(Ω.subgroupOf N) := MulAut.conjNormal
  have hθ : ∀ x : N, θ x = 1 → ∀ w ∈ Ω, w * (x : G) = (x : G) * w := by
    intro x hx w hw
    have h1 := congrArg (fun φ : MulAut ↥(Ω.subgroupOf N) =>
      (((φ ⟨⟨w, hΩN hw⟩, Subgroup.mem_subgroupOf.mpr hw⟩ : ↥(Ω.subgroupOf N)) : N) : G)) hx
    simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    calc w * (x : G) = ((x : G) * w * (x : G)⁻¹) * (x : G) := by rw [h1]
      _ = (x : G) * w := by group
  have hθ' : ∀ x : N, (∀ w ∈ Ω, w * (x : G) = (x : G) * w) → θ x = 1 := by
    intro x hx
    refine MulEquiv.ext fun w => Subtype.ext (Subtype.ext ?_)
    simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    rw [← hx _ (Subgroup.mem_subgroupOf.mp w.2), mul_inv_cancel_right]
  have hV8 : Nat.card ↥(Ω.subgroupOf N) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩN).toEquiv]
    exact natCard_omegaIn_one_of_pos dD.e hk
  have hV2 : ∀ v : ↥(Ω.subgroupOf N), v * v = 1 := fun v => Subtype.ext (Subtype.ext
    ((mem_omegaIn_one_iff hDc).mp (Subgroup.mem_subgroupOf.mp v.2)).2)
  have h168 : Nat.card (MulAut ↥(Ω.subgroupOf N)) = 168 :=
    CFSG.OddStandard.ChengHeld.card_mulAut_elemAb8 hV8 hV2
  have hNp : IsPGroup 2 N := F.S.isPGroup'.to_le inf_le_left
  have hPp : IsPGroup 2 θ.range := hNp.of_surjective θ.rangeRestrict θ.rangeRestrict_surjective
  have hdvd8 : ∀ H : Subgroup (MulAut ↥(Ω.subgroupOf N)), H ≤ θ.range → Nat.card H ∣ 8 := by
    intro H hH
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp (hPp.to_le hH)
    have hd : Nat.card H ∣ 8 * 21 := by
      rw [show 8 * 21 = 168 by norm_num, ← h168]; exact Subgroup.card_subgroup_dvd_card _
    rw [ha] at hd ⊢
    exact (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 21)).dvd_of_dvd_mul_right hd
  set tN : N := ⟨dD.t, htN⟩
  set uN : N := ⟨dD.u, huN⟩
  set uvN : N := ⟨dD.uv, huvN⟩
  have hθuv1 : θ uvN ≠ 1 := fun h1 => huvR (hθ uvN h1)
  have hnc : θ tN * θ uN ≠ θ uN * θ tN := by
    intro hc
    have h1 : θ (tN⁻¹ * uN⁻¹ * tN * uN) = 1 := by
      simp only [map_mul, map_inv]
      rw [mul_assoc _ (θ tN) (θ uN), hc]
      group
    apply hθuv1
    have h2 : (tN⁻¹ * uN⁻¹ * tN * uN : N) = uvN := Subtype.ext htu
    rw [← h2]
    exact h1
  have hP8 : Nat.card θ.range = 8 :=
    card_eq_eight_of_dvd (hdvd8 _ le_rfl) ⟨tN, rfl⟩ ⟨uN, rfl⟩ hnc
  have hle : Subgroup.closure {θ uvN, θ tN, θ uN} ≤ θ.range := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl) <;> exact ⟨_, rfl⟩
  have hgenP : θ.range ≤ Subgroup.closure {θ uvN, θ tN, θ uN} :=
    (Subgroup.eq_of_le_of_card_ge hle (by
      rw [hP8, card_eq_eight_of_dvd (hdvd8 _ hle) (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)) hnc])).ge
  have hmem : θ ⟨n, hn⟩ ∈ (Subgroup.closure ({uvN, tN, uN} : Set N)).map θ := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
    exact hgenP ⟨_, rfl⟩
  obtain ⟨w, hw, hθw⟩ := hmem
  have hwG : (w : G) ∈ Subgroup.closure ({dD.uv, dD.t, dD.u} : Set G) := by
    have h1 := Subgroup.mem_map_of_mem N.subtype hw
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton]
      at h1
    exact h1
  obtain ⟨i, j, l, hijl⟩ := dD.mem_closure_iff_d8.mp hwG
  refine ⟨i, j, l, fun w' hw' => ?_⟩
  have h1 : θ (w⁻¹ * ⟨n, hn⟩) = 1 := by rw [map_mul, map_inv, hθw, inv_mul_cancel]
  have h2 := hθ (w⁻¹ * ⟨n, hn⟩) h1 w' hw'
  rw [← hijl]
  simpa using h2

theorem StrothWeakTypeData.d8_conj_mem_omegaIn (dD : StrothWeakTypeData D τ) (i j l : Bool)
    {w : G} (hw : w ∈ omegaIn 1 D) :
    (dD.d8 i j l)⁻¹ * w * dD.d8 i j l ∈ omegaIn 1 D := by
  have hN : dD.d8 i j l ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    normalizer_le_normalizer_omegaIn D (dD.closure_le_normalizer (dD.d8_mem i j l))
  exact (Subgroup.mem_normalizer_iff''.mp hN w).mp hw

theorem StrothFrame.IsD.conj_le_R_of_inf_le (h : F.IsD D dD) (hk : ∀ i, 1 ≤ τ.k i)
    (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w)
    (hsq : ∀ x ∈ D, x * x = 1 → ∃ y ∈ D, y * y = x)
    {w₁ w₂ : G} (hw₁Ω : w₁ ∈ omegaIn 1 D) (hw₁ : ∃ d ∈ D, d ^ 4 = w₁) (hw₂ : w₂ ≠ w₁)
    (huw : dD.u * w₁ * dD.u⁻¹ = w₂) (huv₂ : dD.uv * w₂ = w₂ * dD.uv)
    (ht₂ : dD.t * w₂ = w₂ * dD.t) {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G))
    (hA : D.map (MulAut.conj g).toMonoidHom ⊓ ((F.S : Subgroup G) ⊓
      Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ D) :
    ∀ y ∈ D.map (MulAut.conj g).toMonoidHom, ∀ w ∈ omegaIn 1 D, w * y = y * w := by
  classical
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  set Ω : Subgroup G := omegaIn 1 D with hΩ
  set C : Subgroup G := Subgroup.centralizer (Ω : Set G) with hC
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDN : D ≤ N := le_inf h.le_S Subgroup.le_normalizer
  set K : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hK
  have hmemK : ∀ k ∈ K, ∃ d ∈ D, k = g * d * g⁻¹ := by
    rintro k ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  have hconjK : ∀ d ∈ D, g * d * g⁻¹ ∈ K := fun d hd => ⟨d, hd, rfl⟩
  have hKN : K ≤ N := by
    intro k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    exact (Subgroup.mem_normalizer_iff.mp hgN d).mp (hDN hd)
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := hmemK a ha
    obtain ⟨d', hd', rfl⟩ := hmemK b hb
    calc g * d * g⁻¹ * (g * d' * g⁻¹) = g * (d * d') * g⁻¹ := by group
      _ = g * (d' * d) * g⁻¹ := by rw [hcommD _ hd _ hd']
      _ = g * d' * g⁻¹ * (g * d * g⁻¹) := by group
  have hKnorm : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    have hxN : g⁻¹ * x * g ∈ N := (Subgroup.mem_normalizer_iff''.mp hgN x).mp hx
    have hd' : (g⁻¹ * x * g) * d * (g⁻¹ * x * g)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hxN.2 d).mp hd
    refine ⟨_, hd', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcardK : Nat.card K = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  by_contra hKR
  obtain ⟨-, hcount⟩ := h.exists_mem_uv_mul_of_normal hk huvR hKN hKnorm hKc hKR
  have hKCD : K ⊓ C ≤ K ⊓ D := fun z hz => ⟨hz.1, hA ⟨hz.1, hKN hz.1, hz.2⟩⟩
  have hcount' : Nat.card K ≤ 4 * Nat.card ↥(K ⊓ D) :=
    hcount.trans (Nat.mul_le_mul_left 4 (Subgroup.card_le_of_le hKCD))
  set B : Subgroup D := (K ⊓ D).subgroupOf D with hB
  have hBcard : Nat.card B = Nat.card ↥(K ⊓ D) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : K ⊓ D ≤ D)).toEquiv
  have hBidx4 : B.index ∣ 4 := by
    have hmul := B.card_mul_index
    have hd : B.index ∣ 2 ^ (τ.k 0 + τ.k 1 + τ.k 2) := by
      rw [← dD.card]; exact B.index_dvd_card
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hle4 : B.index ≤ 4 := by
      by_contra hlt
      push Not at hlt
      have : Nat.card B * 5 ≤ Nat.card B * B.index := Nat.mul_le_mul_left _ hlt
      rw [hmul, hBcard] at this
      rw [hBcard] at hpos
      omega
    rw [hjeq] at hle4 ⊢
    have hj2 : j ≤ 2 := by
      by_contra hj2
      have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (Nat.pow_dvd_pow 2 hj2).trans (by norm_num)
  haveI : B.Normal := ⟨fun n _ x => by
    rwa [show x * n * x⁻¹ = n by rw [hDc.is_comm.comm x n, mul_inv_cancel_right]]⟩
  have h4 : ∀ d ∈ D, d ^ 4 ∈ K := by
    intro d hd
    obtain ⟨c, hc⟩ := hBidx4
    have h1 : (⟨d, hd⟩ : D) ^ 4 ∈ B := by
      rw [hc, pow_mul]
      exact Subgroup.pow_mem _ (Subgroup.pow_index_mem B _) _
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa using h2.1
  obtain ⟨d₁, hd₁, hd₁w⟩ := hw₁
  have hw₁K : w₁ ∈ K := hd₁w ▸ h4 d₁ hd₁
  have hconj₂ : ∀ x : G, x * w₂ = w₂ * x → x * w₂ * x⁻¹ = w₂ := fun x hx => by
    rw [hx, mul_inv_cancel_right]
  have hsqK : ∀ k ∈ K, k * k ∈ D := by
    intro k hk'
    obtain ⟨i, j, l, hr⟩ := h.exists_d8_inv_mul_mem hk huvR (hKN hk')
    set a := dD.d8 i j l with ha
    set r := a⁻¹ * k with hr_def
    have hkr : k = a * r := by rw [hr_def, mul_inv_cancel_left]
    cases l with
    | true =>
      exfalso
      have hrw : r * w₁ * r⁻¹ = w₁ := by rw [← hr w₁ hw₁Ω, mul_inv_cancel_right]
      have haw : a * w₁ * a⁻¹ = w₂ := by
        have hu : dD.u * w₁ * dD.u⁻¹ = w₂ := huw
        cases i <;> cases j <;> simp only [ha, StrothWeakTypeData.d8, Bool.false_eq_true,
          ↓reduceIte, one_mul, mul_inv_rev, inv_one, mul_one]
        · exact hu
        · calc dD.t * dD.u * w₁ * (dD.u⁻¹ * dD.t⁻¹) = dD.t * (dD.u * w₁ * dD.u⁻¹) * dD.t⁻¹ := by
                group
            _ = w₂ := by rw [hu, hconj₂ _ ht₂]
        · calc dD.uv * dD.u * w₁ * (dD.u⁻¹ * dD.uv⁻¹) =
                dD.uv * (dD.u * w₁ * dD.u⁻¹) * dD.uv⁻¹ := by group
            _ = w₂ := by rw [hu, hconj₂ _ huv₂]
        · calc dD.uv * (dD.t * dD.u) * w₁ * (dD.u⁻¹ * dD.t⁻¹ * dD.uv⁻¹) =
                dD.uv * (dD.t * (dD.u * w₁ * dD.u⁻¹) * dD.t⁻¹) * dD.uv⁻¹ := by group
            _ = w₂ := by rw [hu, hconj₂ _ ht₂, hconj₂ _ huv₂]
      have hkw : k * w₁ * k⁻¹ = w₂ := by
        rw [hkr]
        calc a * r * w₁ * (a * r)⁻¹ = a * (r * w₁ * r⁻¹) * a⁻¹ := by group
          _ = w₂ := by rw [hrw, haw]
      have hkw' : k * w₁ * k⁻¹ = w₁ := by rw [hKc k hk' w₁ hw₁K, mul_inv_cancel_right]
      exact hw₂ (hkw.symm.trans hkw')
    | false =>
      have ha2 : a * a = 1 := by
        rw [ha, dD.d8_mul_self, Bool.false_and, dD.d8_fff]
      have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
      have hk2 : k * k = (a * r * a⁻¹) * r := by
        rw [hkr, ha']
        group
      have hcent : ∀ w ∈ Ω, w * (k * k) = (k * k) * w := by
        intro w hw
        have hw' : a⁻¹ * w * a ∈ Ω := dD.d8_conj_mem_omegaIn i j false hw
        have h1 : (a * r * a⁻¹) * w = w * (a * r * a⁻¹) := by
          have h2 := hr _ hw'
          calc a * r * a⁻¹ * w = a * (r * (a⁻¹ * w * a)) * a⁻¹ := by group
            _ = a * ((a⁻¹ * w * a) * r) * a⁻¹ := by rw [← h2]
            _ = w * (a * r * a⁻¹) := by group
        rw [hk2]
        calc w * (a * r * a⁻¹ * r) = (w * (a * r * a⁻¹)) * r := by group
          _ = (a * r * a⁻¹) * (w * r) := by rw [← h1, mul_assoc]
          _ = (a * r * a⁻¹) * (r * w) := by rw [hr w hw]
          _ = a * r * a⁻¹ * r * w := by group
      exact hA ⟨K.mul_mem hk' hk', N.mul_mem (hKN hk') (hKN hk'),
        Subgroup.mem_centralizer_iff.mpr fun w hw => hcent w hw⟩
  set T : Set G := (fun d => g * d * g⁻¹) '' (Ω : Set G) with hT
  have hTΩ : T ⊆ (Ω : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    obtain ⟨hdD, hd2⟩ := (mem_omegaIn_one_iff hDc).mp hd
    obtain ⟨e, heD, rfl⟩ := hsq d hdD hd2
    have h1 : g * (e * e) * g⁻¹ = (g * e * g⁻¹) * (g * e * g⁻¹) := by group
    have h2 : g * (e * e) * g⁻¹ ∈ D := by rw [h1]; exact hsqK _ (hconjK e heD)
    refine mem_omegaIn_one_of_mul_self h2 ?_
    calc g * (e * e) * g⁻¹ * (g * (e * e) * g⁻¹) = g * ((e * e) * (e * e)) * g⁻¹ := by group
      _ = 1 := by rw [hd2, mul_one, mul_inv_cancel]
  have hTcard : T.ncard = (Ω : Set G).ncard :=
    Set.ncard_image_of_injective _ (MulAut.conj g).injective
  have hTeq : T = (Ω : Set G) := Set.eq_of_subset_of_ncard_le hTΩ hTcard.ge
  apply hKR
  intro y hy w hw
  have hwT : w ∈ T := by rw [hTeq]; exact hw
  obtain ⟨d, hd, rfl⟩ := hwT
  exact hKc _ (hconjK d (omegaIn_le 1 D hd)) y hy

theorem StrothFrame.IsD.mem_normalizer_omegaIn_of_cases (h : F.IsD D dD) (hτ : τ.m ≠ τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) → τ.m = τ.n)
    (hA : ∀ g ∈ Subgroup.normalizer
        (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G),
      D.map (MulAut.conj g).toMonoidHom ⊓ ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ D →
      ∀ y ∈ D.map (MulAut.conj g).toMonoidHom, ∀ w ∈ omegaIn 1 D, w * y = y * w)
    (hB : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
      (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) →
      4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G)) < Nat.card D)
    {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  classical
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  set Ω : Subgroup G := omegaIn 1 D with hΩ
  set C : Subgroup G := Subgroup.centralizer (Ω : Set G) with hC
  set R : Subgroup G := N ⊓ C with hRdef
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hDc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hDN : D ≤ N := le_inf h.le_S Subgroup.le_normalizer
  have hDC : D ≤ C := fun x hx => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    hcommD _ (omegaIn_le 1 D hw) _ hx
  have hDR : D ≤ R := le_inf hDN hDC
  have huvN : dD.uv ∈ N := ⟨h.uv_eq ▸ F.uv_mem_S, dD.uv_mem⟩
  set K : Subgroup G := D.map (MulAut.conj g).toMonoidHom with hK
  have hmemK : ∀ k ∈ K, ∃ d ∈ D, k = g * d * g⁻¹ := by
    rintro k ⟨d, hd, rfl⟩
    exact ⟨d, hd, rfl⟩
  have hKN : K ≤ N := by
    intro k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    exact (Subgroup.mem_normalizer_iff.mp hgN d).mp (hDN hd)
  have hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨d, hd, rfl⟩ := hmemK a ha
    obtain ⟨d', hd', rfl⟩ := hmemK b hb
    calc g * d * g⁻¹ * (g * d' * g⁻¹) = g * (d * d') * g⁻¹ := by group
      _ = g * (d' * d) * g⁻¹ := by rw [hcommD _ hd _ hd']
      _ = g * d' * g⁻¹ * (g * d * g⁻¹) := by group
  have hKnorm : ∀ x ∈ N, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
    intro x hx k hk'
    obtain ⟨d, hd, rfl⟩ := hmemK k hk'
    have hxN : g⁻¹ * x * g ∈ N := (Subgroup.mem_normalizer_iff''.mp hgN x).mp hx
    have hd' : (g⁻¹ * x * g) * d * (g⁻¹ * x * g)⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hxN.2 d).mp hd
    refine ⟨_, hd', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hcardK : Nat.card K = Nat.card D :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hKR : ∀ y ∈ K, ∀ w ∈ Ω, w * y = y * w := by
    by_cases hcase : K ⊓ R ≤ D
    · exact hA g hgN hcase
    by_contra hKR
    obtain ⟨⟨y, hyK, hyR⟩, hcount0⟩ := h.exists_mem_uv_mul_of_normal hk huvR hKN hKnorm hKc hKR
    have hcount : Nat.card K ≤ 4 * Nat.card ↥(K ⊓ C) := hcount0
    set x := dD.uv⁻¹ * y with hx_def
    have hxR : x ∈ R := ⟨N.mul_mem (N.inv_mem huvN) (hKN hyK),
      Subgroup.mem_centralizer_iff.mpr fun w hw => hyR w hw⟩
    have hyx : dD.uv * x = y := by rw [hx_def, mul_inv_cancel_left]
    set Q : Subgroup G := K ⊓ R with hQ
    have hKCR : K ⊓ C = Q := by
      ext z
      exact ⟨fun hz => ⟨hz.1, hKN hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
    have hQR : Q ≤ R := inf_le_right
    have hQc : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb => hKc a ha.1 b hb.1
    have hb := hB x hxR Q hQR hcase hQc
    have e1 := Subgroup.relIndex_mul_card (H := D) (K := Q)
    have hDQ : D ⊓ Q = K ⊓ D := by
      ext z
      exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hDR hz.2⟩⟩
    rw [hDQ] at e1
    have hKD : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G) := by
      intro z hz
      refine ⟨⟨hz.2, Subgroup.mem_centralizer_iff.mpr ?_⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      · rintro _ rfl
        rw [hyx]
        exact hKc _ hyK _ hz.1
      · intro q hq
        exact hKc _ hq.1 _ hz.1
    have h1 := Subgroup.card_le_of_le hKD
    rw [hKCR] at hcount
    have h2 : Nat.card K ≤ 4 * (D.relIndex Q * Nat.card ↥(K ⊓ D)) := by rw [e1]; exact hcount
    have h3 : 4 * (D.relIndex Q * Nat.card ↥(K ⊓ D)) ≤ 4 * D.relIndex Q *
        Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer (Q : Set G)) := by
      rw [← mul_assoc]
      exact Nat.mul_le_mul_left _ h1
    omega
  have hKeq : K = D := by
    by_contra hne
    refine hτ (h226 K (fun y hy => ⟨hKN hy, Subgroup.mem_centralizer_iff.mpr
      fun w hw => hKR y hy w hw⟩) (fun x hx b hb => hKnorm x hx.1 b hb) hne ⟨g, rfl⟩)
  have hgD : g ∈ Subgroup.normalizer (D : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hKeq]; exact ⟨x, hx, rfl⟩
    · rw [← hKeq] at hx
      obtain ⟨d, hd, hdx⟩ := hmemK _ hx
      have : x = d := by simpa using hdx
      exact this ▸ hd
  exact normalizer_le_normalizer_omegaIn D hgD

theorem exists_mul_self_eq_of_two_le {D : Subgroup G} {k : Fin 3 → ℕ}
    (e : Additive D ≃+ Torus k) (hk : ∀ i, 2 ≤ k i) {x : G} (hx : x ∈ D) (hx2 : x * x = 1) :
    ∃ y ∈ D, y * y = x := by
  classical
  set v := e (Additive.ofMul (⟨x, hx⟩ : D)) with hv
  have hv2 : v + v = 0 := by
    rw [hv, ← map_add, ← ofMul_mul,
      show (⟨x, hx⟩ : D) * ⟨x, hx⟩ = 1 from Subtype.ext hx2, ofMul_one, map_zero]
  let w : Torus k := fun i => if v i = 0 then 0 else 2 ^ (k i - 2)
  have hw : w + w = v := by
    funext i
    by_cases h0 : v i = 0
    · simp [w, h0]
    · have h1 := (zmod_two_pow_eq_zero_or_of_add_self (v i) (congrFun hv2 i)).resolve_left h0
      simp only [Pi.add_apply, w, if_neg h0]
      rw [h1, ← two_mul, ← pow_succ']
      congr 1
      have := hk i
      omega
  refine ⟨((Additive.toMul (e.symm w) : D) : G), (Additive.toMul (e.symm w) : D).2, ?_⟩
  have h2 : (Additive.toMul (e.symm w) : D) * Additive.toMul (e.symm w) = ⟨x, hx⟩ := by
    apply Additive.ofMul.injective
    apply e.injective
    rw [ofMul_mul, map_add, ofMul_toMul, AddEquiv.apply_symm_apply, hw]
  simpa using congrArg Subtype.val h2

theorem StrothFrame.IsD.hA_of_torus (h : F.IsD D dD) (hk2 : ∀ i, 2 ≤ τ.k i)
    (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w) {v₁ v₂ z : Torus τ.k}
    (hz : 4 • z = v₁) (hv₁ : v₁ + v₁ = 0) (hne : v₂ ≠ v₁) (hu : τ.action.φu v₁ = v₂)
    (huv : τ.action.φuv v₂ = v₂) (ht : τ.action.φt v₂ = v₂) :
    ∀ g ∈ Subgroup.normalizer
        (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G),
      D.map (MulAut.conj g).toMonoidHom ⊓ ((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ D →
      ∀ y ∈ D.map (MulAut.conj g).toMonoidHom, ∀ w ∈ omegaIn 1 D, w * y = y * w :=
  fun _ hgN hA => h.conj_le_R_of_inf_le (fun i => le_trans (by norm_num) (hk2 i)) huvR
    (fun _ hx hx2 => exists_mul_self_eq_of_two_le dD.e hk2 hx hx2)
    (w₁ := dD.ofTorus v₁) (w₂ := dD.ofTorus v₂)
    (mem_omegaIn_one_of_mul_self (dD.ofTorus_mem v₁)
      (by rw [← dD.ofTorus_add, hv₁, dD.ofTorus_zero]))
    ⟨dD.ofTorus z, dD.ofTorus_mem z, by rw [← dD.ofTorus_nsmul, hz]⟩
    (fun heq => hne (dD.ofTorus_inj heq))
    (by rw [dD.u_mul_ofTorus, hu, mul_inv_cancel_right])
    (by rw [dD.uv_mul_ofTorus, huv]) (by rw [dD.t_mul_ofTorus, ht]) hgN hA

theorem not_commute_mul_of_commute {w b x : G} (hwb : ¬ w * b = b * w) (hx : w * x = x * w) :
    ¬ w * (b * x) = b * x * w := by
  intro h
  apply hwb
  have h1 : w * b * x = b * w * x := by
    calc w * b * x = w * (b * x) := by group
      _ = b * x * w := h
      _ = b * (x * w) := by group
      _ = b * (w * x) := by rw [hx]
      _ = b * w * x := by group
  exact mul_right_cancel h1

theorem StrothWeakTypeData.mul_self_eq_one_of_inv_shape (dD : StrothWeakTypeData D τ)
    (hn : 3 ≤ τ.n) {e : G} {j t : ℕ} (hj : j = 2 ^ (τ.n - 1) * t)
    (hc : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (ha : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ j)
    (hb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ j) {d : G} (hd : d ∈ D)
    (hde : d * e = e * d) : d * d = 1 := by
  classical
  let M : IntMat := !![-1, 0, 0; 0, (j : ℤ) - 1, 0; 0, 0, (j : ℤ) - 1]
  have hM : Compat τ.k M := Compat.of_witness (C := M) (fun i j' => by
    fin_cases i <;> fin_cases j' <;> simp [M])
  set φ := matAct τ.k M hM with hφ
  have hcoef : ∀ (g : G) (q : ℕ), g⁻¹ * g ^ q = g ^ ((q : ℤ) - 1) := fun g q => by
    rw [zpow_sub_one, zpow_natCast, ← (Commute.self_pow g q).inv_left.eq]
  have hcφ : e⁻¹ * (dD.c : G) * e = dD.ofTorus (φ Torus.c) := by
    rw [hc, show Torus.c = Torus.ofInt τ.k ![1, 0, 0] by
      funext i; fin_cases i <;> simp [Torus.ofInt, Torus.c, gen, Pi.single_apply],
      matAct_ofInt, dD.ofTorus_ofInt]
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have haφ : e⁻¹ * (dD.a : G) * e = dD.ofTorus (φ Torus.a) := by
    rw [ha, show Torus.a = Torus.ofInt τ.k ![0, 1, 0] by
      funext i; fin_cases i <;> simp [Torus.ofInt, Torus.a, gen, Pi.single_apply],
      matAct_ofInt, dD.ofTorus_ofInt, hcoef]
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hbφ : e⁻¹ * (dD.b : G) * e = dD.ofTorus (φ Torus.b) := by
    rw [hb, show Torus.b = Torus.ofInt τ.k ![0, 0, 1] by
      funext i; fin_cases i <;> simp [Torus.ofInt, Torus.b, gen, Pi.single_apply],
      matAct_ofInt, dD.ofTorus_ofInt, hcoef]
    simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  obtain ⟨v, rfl⟩ := dD.exists_ofTorus hd
  obtain ⟨x, rfl⟩ := Torus.exists_ofInt v
  have hfix : φ (Torus.ofInt τ.k x) = Torus.ofInt τ.k x := by
    apply dD.ofTorus_inj
    rw [← dD.conj_ofTorus_of_gens hcφ haφ hbφ, mul_assoc, hde, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have hMx : M.mulVec x = ![-x 0, ((j : ℤ) - 1) * x 1, ((j : ℤ) - 1) * x 2] := by
    funext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hφ, matAct_ofInt, hMx, Torus.ofInt_eq_ofInt_iff] at hfix
  rw [dD.ofTorus_mul_self, dD.ofTorus_eq_one_iff, ← Torus.ofInt_add, Torus.ofInt_eq_zero_iff]
  have hodd : IsCoprime ((2 : ℤ) ^ (τ.n - 1)) (2 ^ (τ.n - 2) * t - 1) := by
    apply IsCoprime.pow_left
    obtain ⟨r, hr⟩ : ∃ r, τ.n - 2 = r + 1 := ⟨τ.n - 3, by omega⟩
    rw [hr]
    exact ⟨2 ^ r * t, -1, by ring⟩
  have hjz : ((j : ℕ) : ℤ) - 2 = 2 * (2 ^ (τ.n - 2) * t - 1) := by
    rw [hj]
    push_cast
    rw [show τ.n - 1 = (τ.n - 2) + 1 by omega, pow_succ]
    ring
  have hcoord : ∀ y : ℤ, (2 : ℤ) ^ τ.n ∣ y - ((j : ℤ) - 1) * y → (2 : ℤ) ^ τ.n ∣ y + y := by
    intro y h1
    have e : y - ((j : ℤ) - 1) * y = -(2 * ((2 ^ (τ.n - 2) * t - 1) * y)) := by
      rw [show y - ((j : ℤ) - 1) * y = -((((j : ℕ) : ℤ) - 2) * y) by ring, hjz]
      ring
    rw [e, dvd_neg, show τ.n = (τ.n - 1) + 1 by omega, pow_succ'] at h1
    have h3 := (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h1
    have h4 := hodd.dvd_of_dvd_mul_left h3
    rw [show τ.n = (τ.n - 1) + 1 by omega, pow_succ', ← two_mul]
    exact mul_dvd_mul_left 2 h4
  intro i
  fin_cases i
  · have h0 := (hfix 0).dvd
    simp only [Matrix.cons_val_zero] at h0
    simp only [Pi.add_apply, Fin.zero_eta, Fin.isValue]
    rwa [show x 0 - -x 0 = x 0 + x 0 by ring] at h0
  · have h0 := (hfix 1).dvd
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h0
    simp only [Pi.add_apply, Fin.mk_one, Fin.isValue]
    exact hcoord _ h0
  · have h0 := (hfix 2).dvd
    simp only [Matrix.cons_val_two, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.tail_cons,
      Matrix.head_cons] at h0
    simp only [Pi.add_apply, Fin.reduceFinMk, Fin.isValue]
    have hk2 : τ.k 2 = τ.n := τ.k_two
    rw [hk2] at h0 ⊢
    exact hcoord _ h0

open scoped Pointwise in
theorem mem_or_inv_mul_mem_of_mem_sup_zpowers {D : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D) {y : G}
    (hy : y ∈ D ⊔ Subgroup.zpowers e) : y ∈ D ∨ e⁻¹ * y ∈ D := by
  have hle : Subgroup.zpowers e ≤ Subgroup.normalizer (D : Set G) :=
    (Subgroup.zpowers_le).mpr he
  have hy' : y ∈ ((D : Set G) * (Subgroup.zpowers e : Set G)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left D _ hle]
    exact hy
  obtain ⟨d, hd, z, hz, rfl⟩ := hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have he2' : e ^ (2 : ℤ) ∈ D := by rw [zpow_two]; exact he2
  rcases Int.even_or_odd' k with ⟨j, hj | hj⟩
  · left
    rw [hj, zpow_mul]
    exact D.mul_mem hd (D.zpow_mem he2' j)
  · right
    have h1 : e⁻¹ * (d * e ^ (2 * j + 1)) = (e⁻¹ * d * e) * (e ^ (2 : ℤ)) ^ j := by
      rw [← zpow_mul, zpow_add_one, ← (Commute.self_zpow e (2 * j)).eq]
      group
    rw [hj, h1]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff''.mp he d).mp hd) (D.zpow_mem he2' j)

theorem relIndex_le_two_of_le_sup_zpowers {D : Subgroup G} {e : G}
    (he : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D) {Q : Subgroup G}
    (hQ : Q ≤ D ⊔ Subgroup.zpowers e) : D.relIndex Q ≤ 2 := by
  classical
  have e1 := Subgroup.relIndex_mul_card (H := D) (K := Q)
  have hpos : 0 < Nat.card ↥(D ⊓ Q) := Nat.card_pos
  by_cases hQD : Q ≤ D
  · rw [Subgroup.relIndex_eq_one.mpr hQD]
    norm_num
  obtain ⟨q₀, hq₀Q, hq₀D⟩ := SetLike.not_le_iff_exists.mp hQD
  have hq₀ : e⁻¹ * q₀ ∈ D := (mem_or_inv_mul_mem_of_mem_sup_zpowers he he2 (hQ hq₀Q)).resolve_left
    hq₀D
  let f : Bool × ↥(D ⊓ Q) → ↥Q := fun p =>
    if p.1 then ⟨q₀ * p.2, Q.mul_mem hq₀Q p.2.2.2⟩ else ⟨p.2, p.2.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers he he2 (hQ hy) with hyD | hyD
    · exact ⟨(false, ⟨y, hyD, hy⟩), rfl⟩
    · have h1 : q₀⁻¹ * y ∈ D := by
        have := D.mul_mem (D.inv_mem hq₀) hyD
        rwa [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] at this
      refine ⟨(true, ⟨q₀⁻¹ * y, h1, Q.mul_mem (Q.inv_mem hq₀Q) hy⟩), ?_⟩
      simp [f]
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hcard
  rw [← e1] at hcard
  have : D.relIndex Q * Nat.card ↥(D ⊓ Q) ≤ 2 * Nat.card ↥(D ⊓ Q) := hcard
  exact Nat.le_of_mul_le_mul_right this hpos

theorem two_pow_mul_card_inf_centralizer_le {D H : Subgroup G}
    (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {s : ℕ} (hDs : Nat.card D = 2 ^ s) (hHD : H ≤ D)
    {b : G} (hb : b ∈ Subgroup.normalizer (D : Set G)) {c : G} (hc : c ∈ H) {j : ℕ}
    (hcb : ¬ c ^ 2 ^ (j - 1) * b = b * c ^ 2 ^ (j - 1)) :
    2 ^ j * Nat.card ↥(H ⊓ Subgroup.centralizer ({b} : Set G)) ≤ Nat.card H := by
  classical
  let φ : ↥H →* ↥D := (commHom hD hb).comp (Subgroup.inclusion hHD)
  have hker : Nat.card φ.ker = Nat.card ↥(H ⊓ Subgroup.centralizer ({b} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : H) : G), (x : H).2, Subgroup.mem_centralizer_singleton_iff.mpr
          ((commHom_eq_one_iff hD hb _).mp (MonoidHom.mem_ker.mp x.2))⟩
        invFun := fun x => ⟨⟨x, (Subgroup.mem_inf.mp x.2).1⟩, MonoidHom.mem_ker.mpr
          ((commHom_eq_one_iff hD hb ⟨x, hHD (Subgroup.mem_inf.mp x.2).1⟩).mpr
            (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp x.2).2))⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
  have hsplit := Subgroup.card_ker_mul_card_range φ
  rw [hker] at hsplit
  set r : ↥D := φ ⟨c, hc⟩ with hr
  have hr_pow : r ^ 2 ^ (j - 1) ≠ 1 := by
    intro h1
    rw [hr, ← map_pow] at h1
    apply hcb
    have h2 := (commHom_eq_one_iff hD hb _).mp h1
    simpa using h2
  have hord_dvd : orderOf r ∣ 2 ^ s := by rw [← hDs]; exact orderOf_dvd_natCard r
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord_dvd
  have htj : j ≤ t := by
    by_contra hlt
    push Not at hlt
    apply hr_pow
    rw [← orderOf_dvd_iff_pow_eq_one, ht]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hle : 2 ^ j ≤ Nat.card φ.range := by
    calc 2 ^ j ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) htj
      _ = orderOf r := ht.symm
      _ = orderOf (⟨r, ⟨c, hc⟩, rfl⟩ : φ.range) := (Subgroup.orderOf_mk _ _).symm
      _ ≤ Nat.card φ.range := Nat.le_of_dvd Nat.card_pos (orderOf_dvd_natCard _)
  calc 2 ^ j * Nat.card ↥(H ⊓ Subgroup.centralizer ({b} : Set G))
      ≤ Nat.card φ.range * Nat.card ↥(H ⊓ Subgroup.centralizer ({b} : Set G)) :=
        Nat.mul_le_mul_right _ hle
    _ = Nat.card H := by rw [mul_comm]; exact hsplit

theorem four_mul_card_inf_centralizer_le {D : Subgroup G}
    (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) {s : ℕ} (hDs : Nat.card D = 2 ^ s) {e : G}
    (he : e ∈ Subgroup.normalizer (D : Set G)) {d₁ d₂ : G} (hd₁ : d₁ ∈ D) (hd₂ : d₂ ∈ D)
    (h₁ : e⁻¹ * d₁ * e * d₁⁻¹ ≠ 1) (h₂ : e⁻¹ * d₂ * e * d₂⁻¹ ≠ 1)
    (h₁₂ : e⁻¹ * d₁ * e * d₁⁻¹ ≠ e⁻¹ * d₂ * e * d₂⁻¹) :
    4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G)) ≤ Nat.card D := by
  classical
  have hsplit := card_inf_centralizer_mul_card_range hD he
  set ρ := (commHom hD he).range with hρ
  have hdvd : Nat.card ρ ∣ 2 ^ s := by rw [← hDs]; exact Subgroup.card_subgroup_dvd_card ρ
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h3 : 3 ≤ Nat.card ρ := by
    set r₁ := commHom hD he ⟨d₁, hd₁⟩ with hr₁
    set r₂ := commHom hD he ⟨d₂, hd₂⟩ with hr₂
    have hne1 : r₁ ≠ 1 := fun h0 => h₁ (by
      have := congrArg Subtype.val h0; simpa [hr₁, coe_commHom] using this)
    have hne2 : r₂ ≠ 1 := fun h0 => h₂ (by
      have := congrArg Subtype.val h0; simpa [hr₂, coe_commHom] using this)
    have hne12 : r₁ ≠ r₂ := fun h0 => h₁₂ (by
      have := congrArg Subtype.val h0; simpa [hr₁, hr₂, coe_commHom] using this)
    have hS : ({1, r₁, r₂} : Set ↥D) ⊆ (ρ : Set ↥D) := by
      rintro z (rfl | rfl | rfl)
      · exact ρ.one_mem
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    have hc3 : ({1, r₁, r₂} : Set ↥D).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by simp [hne1.symm, hne2.symm]), Set.ncard_pair hne12]
    calc 3 = ({1, r₁, r₂} : Set ↥D).ncard := hc3.symm
      _ ≤ (ρ : Set ↥D).ncard := Set.ncard_le_ncard hS (Set.toFinite _)
      _ = Nat.card ρ := (Nat.card_coe_set_eq (ρ : Set ↥D)).symm
  have h4 : 4 ≤ Nat.card ρ := by
    rw [ht] at h3 ⊢
    rcases t with _ | _ | t
    · norm_num at h3
    · norm_num at h3
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (t + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G))
      ≤ Nat.card ρ * Nat.card ↥(D ⊓ Subgroup.centralizer ({e} : Set G)) :=
        Nat.mul_le_mul_right _ h4
    _ = Nat.card D := by rw [mul_comm]; exact hsplit

theorem StrothFrame.IsD.hB_of_zpowers (h : F.IsD D dD) {e : G}
    (hRe : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D ⊔ Subgroup.zpowers e)
    (heN : e ∈ Subgroup.normalizer (D : Set G)) (he2 : e * e ∈ D)
    (h1 : 8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D)
    (h2 : 8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * e} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D) :
    ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ Q : Subgroup G, Q ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) → ¬ Q ≤ D →
      (∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) →
      4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G)) < Nat.card D := by
  intro x hx Q hQR hQD _
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  rw [hRe] at hx hQR
  have hidx := relIndex_le_two_of_le_sup_zpowers heN he2 hQR
  obtain ⟨q₀, hq₀Q, hq₀D⟩ := SetLike.not_le_iff_exists.mp hQD
  have hq₀ : e⁻¹ * q₀ ∈ D :=
    (mem_or_inv_mul_mem_of_mem_sup_zpowers heN he2 (hQR hq₀Q)).resolve_left hq₀D
  have hCQ : D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer (Q : Set G) ≤
      D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer ({e} : Set G) := by
    intro z hz
    refine ⟨hz.1, ?_⟩
    have hzq : z ∈ D ⊓ Subgroup.centralizer ({e * (e⁻¹ * q₀)} : Set G) := by
      rw [mul_inv_cancel_left]
      exact ⟨hz.1.1, Subgroup.mem_centralizer_singleton_iff.mpr
        ((Subgroup.mem_centralizer_iff.mp hz.2 q₀ hq₀Q).symm)⟩
    rw [inf_centralizer_mul_of_mem hcommD hq₀] at hzq
    exact hzq.2
  have hcard := Subgroup.card_le_of_le hCQ
  have hbound : 8 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
      Subgroup.centralizer ({e} : Set G)) < Nat.card D := by
    rcases mem_or_inv_mul_mem_of_mem_sup_zpowers heN he2 hx with hxD | hxD
    · rwa [inf_centralizer_mul_of_mem hcommD hxD]
    · have hx' : dD.uv * x = dD.uv * e * (e⁻¹ * x) := by group
      rwa [hx', inf_centralizer_mul_of_mem hcommD hxD]
  calc 4 * D.relIndex Q * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer (Q : Set G))
      ≤ 4 * 2 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({e} : Set G)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 4 hidx) hcard
    _ < Nat.card D := by omega

end CFSG.CGT.Stroth77
