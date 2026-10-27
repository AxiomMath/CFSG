module

public import CFSG.CGT.Stroth77.Section41Lemmas

import CFSG.CGT.Stroth77.Arch76FrameChar

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

section Omega

variable {G : Type} [Group G] [Finite G] {D : Subgroup G}

theorem natCard_two_torsion_torus_of_pos {k : Fin 3 → ℕ} (hk : ∀ i, 1 ≤ k i) :
    Nat.card {w : Torus k // 2 • w = 0} = 8 := by
  have e : {w : Torus k // 2 • w = 0} ≃ ∀ i, {z : ZMod (2 ^ k i) // 2 • z = 0} :=
    (Equiv.subtypeEquivRight fun w => by
      rw [funext_iff]; simp only [Pi.smul_apply, Pi.zero_apply]).trans
      (Equiv.subtypePiEquivPi)
  have hm : ∀ i, k i = (k i - 1) + 1 := fun i => by have := hk i; omega
  rw [Nat.card_congr e, Nat.card_pi, Fin.prod_univ_three,
    natCard_two_torsion_zmod (n := k 0 - 1) (congrArg (2 ^ ·) (hm 0)),
    natCard_two_torsion_zmod (n := k 1 - 1) (congrArg (2 ^ ·) (hm 1)),
    natCard_two_torsion_zmod (n := k 2 - 1) (congrArg (2 ^ ·) (hm 2))]
  norm_num

variable {k : Fin 3 → ℕ} (e : Additive D ≃+ Torus k)

include e in
theorem natCard_omegaIn_one_of_pos (hk : ∀ i, 1 ≤ k i) : Nat.card (omegaIn 1 D) = 8 := by
  have hD : IsMulCommutative D := ⟨⟨fun x y => Additive.ofMul.injective (e.injective (by
    simp only [ofMul_mul, map_add]; exact add_comm _ _))⟩⟩
  let E1 : ↥(omegaIn 1 D) ≃ {y : D // y * y = 1} :=
    { toFun := fun x => ⟨⟨x, ((mem_omegaIn_one_iff hD).mp x.2).1⟩,
        Subtype.ext ((mem_omegaIn_one_iff hD).mp x.2).2⟩
      invFun := fun y => ⟨y.1, mem_omegaIn_one_of_mul_self y.1.2 (congrArg Subtype.val y.2)⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  let E2 : {y : D // y * y = 1} ≃ {w : Torus k // 2 • w = 0} :=
    (Additive.ofMul.trans e.toEquiv).subtypeEquiv fun y => mul_self_eq_one_iff_two_nsmul e y
  rw [Nat.card_congr (E1.trans E2), natCard_two_torsion_torus_of_pos hk]

end Omega

section Count

variable {G : Type} [Group G] [Finite G] {F : StrothFrame G} {D : Subgroup G}
  {τ : StrothTypeIndex} {dD : StrothWeakTypeData D τ}

theorem StrothFrame.IsD.exists_mem_uv_mul_of_normal (h : F.IsD D dD) (hk : ∀ i, 1 ≤ τ.k i)
    (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w) {K : Subgroup G}
    (hKN : K ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G))
    (hKnorm : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G), ∀ y ∈ K,
      x * y * x⁻¹ ∈ K)
    (hKc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hKR : ¬ ∀ y ∈ K, ∀ w ∈ omegaIn 1 D, w * y = y * w) :
    (∃ y ∈ K, ∀ w ∈ omegaIn 1 D, w * (dD.uv⁻¹ * y) = dD.uv⁻¹ * y * w) ∧
      Nat.card K ≤
        4 * Nat.card ↥(K ⊓ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) with hN
  set Ω : Subgroup G := omegaIn 1 D with hΩ
  set C : Subgroup G := Subgroup.centralizer (Ω : Set G) with hC
  have hDc : IsMulCommutative D := dD.isMulCommutative
  have hDN : D ≤ N := le_inf h.le_S Subgroup.le_normalizer
  have hΩD : Ω ≤ D := omegaIn_le 1 D
  have hΩN : Ω ≤ N := hΩD.trans hDN
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
  have hθ : ∀ x : N, θ x = 1 ↔ ∀ w ∈ Ω, w * (x : G) = (x : G) * w := by
    intro x
    constructor
    · intro hx w hw
      have h1 := congrArg (fun φ : MulAut ↥(Ω.subgroupOf N) =>
        (((φ ⟨⟨w, hΩN hw⟩, Subgroup.mem_subgroupOf.mpr hw⟩ : ↥(Ω.subgroupOf N)) : N) : G)) hx
      simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
        Subgroup.coe_inv] at h1
      calc w * (x : G) = ((x : G) * w * (x : G)⁻¹) * (x : G) := by rw [h1]
        _ = (x : G) * w := by group
    · intro hx
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
  have hθuv1 : θ uvN ≠ 1 := fun h1 => huvR ((hθ uvN).mp h1)
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
  have hcen' : ∀ p ∈ Subgroup.closure {θ uvN, θ tN, θ uN}, p * θ uvN = θ uvN * p := by
    intro p hp
    induction hp using Subgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rfl
      · rw [← map_mul, ← map_mul]; exact congrArg θ (Subtype.ext dD.uv_comm_t.symm)
      · rw [← map_mul, ← map_mul]; exact congrArg θ (Subtype.ext dD.uv_comm_u.symm)
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx => rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hx, mul_assoc, mul_inv_cancel,
        mul_one]
  have hcen : ∀ p ∈ θ.range, p * θ uvN = θ uvN * p := fun p hp => hcen' p (hgenP hp)
  have hKc' : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := hKc
  set K' : Subgroup N := K.subgroupOf N with hK'
  have hθKle : K'.map θ ≤ θ.range := Subgroup.map_le_range θ K'
  have hθKc : ∀ a ∈ K'.map θ, ∀ b ∈ K'.map θ, a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (hKc' _ (Subgroup.mem_subgroupOf.mp ha) _
      (Subgroup.mem_subgroupOf.mp hb)))
  have hθK4 : Nat.card (K'.map θ) ≤ 4 := by
    have hd := hdvd8 _ hθKle
    have hne : Nat.card (K'.map θ) ≠ 8 := by
      intro h8
      have heq : K'.map θ = θ.range := Subgroup.eq_of_le_of_card_ge hθKle (by rw [h8, hP8])
      exact hnc (hθKc _ (by rw [heq]; exact ⟨tN, rfl⟩) _ (by rw [heq]; exact ⟨uN, rfl⟩))
    have hmem : Nat.card (K'.map θ) ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd, by norm_num⟩
    rw [show Nat.divisors 8 = {1, 2, 4, 8} by decide] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    omega
  refine ⟨?_, ?_⟩
  ·
    have hPp' : IsPGroup 2 θ.range := hPp
    haveI : Group.IsNilpotent θ.range := hPp'.isNilpotent
    haveI hHn : ((K'.map θ).subgroupOf θ.range).Normal := by
      refine ⟨fun z hz p => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hz ⊢
      obtain ⟨y, hy, hyz⟩ := hz
      obtain ⟨x, hx⟩ := p.2
      refine ⟨x * y * x⁻¹, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · simpa using hKnorm x x.2 y (Subgroup.mem_subgroupOf.mp hy)
      · simp [map_mul, map_inv, hx, hyz]
    obtain ⟨y₀, hy₀K, hy₀R⟩ : ∃ y ∈ K, ¬ ∀ w ∈ Ω, w * y = y * w := by
      by_contra hall
      push Not at hall
      exact hKR hall
    have hHne : (K'.map θ).subgroupOf θ.range ≠ ⊥ := by
      intro hbot
      have hkK' : (⟨y₀, hKN hy₀K⟩ : N) ∈ K' := Subgroup.mem_subgroupOf.mpr hy₀K
      have hmem : (⟨θ ⟨y₀, hKN hy₀K⟩, ⟨_, rfl⟩⟩ : θ.range) ∈ (K'.map θ).subgroupOf θ.range :=
        Subgroup.mem_subgroupOf.mpr ⟨_, hkK', rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hy₀R ((hθ _).mp (congrArg Subtype.val hmem))
    obtain ⟨z, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal hHne)
    have hzK : (z : MulAut ↥(Ω.subgroupOf N)) ∈ K'.map θ :=
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp z.2).1
    have hzZ : ∀ d ∈ θ.range, d * (z : MulAut ↥(Ω.subgroupOf N)) = z * d := by
      intro d hd
      have := Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp z.2).2 ⟨d, hd⟩
      exact congrArg Subtype.val this
    have hz1' : ((z : θ.range) : MulAut ↥(Ω.subgroupOf N)) ≠ 1 := fun h1 =>
      hz1 (Subtype.ext (Subtype.ext h1))
    obtain hzc | hzc := eq_one_or_eq_of_central_of_card_eight hP8 ⟨tN, rfl⟩ ⟨uN, rfl⟩ hnc
      ⟨uvN, rfl⟩ hθuv1 hcen ((z : θ.range).2) hzZ
    · exact absurd hzc hz1'
    rw [hzc] at hzK
    obtain ⟨k', hk'K, hk'⟩ := hzK
    refine ⟨k', Subgroup.mem_subgroupOf.mp hk'K, fun w hw => ?_⟩
    have h1 : θ (uvN⁻¹ * k') = 1 := by rw [map_mul, map_inv, hk', inv_mul_cancel]
    exact (hθ (uvN⁻¹ * k')).mp h1 w hw
  ·
    let f : ↥K' →* MulAut ↥(Ω.subgroupOf N) := θ.comp K'.subtype
    have hrange : f.range = K'.map θ := by rw [MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange] at h1
    have hker : Nat.card f.ker ≤ Nat.card ↥(K ⊓ C) := by
      refine Nat.card_le_card_of_injective
        (fun x => ⟨(((x : K') : N) : G), Subgroup.mem_subgroupOf.mp (x : K').2,
          Subgroup.mem_centralizer_iff.mpr fun w hw =>
            ((hθ _).mp (MonoidHom.mem_ker.mp x.2) w hw)⟩) ?_
      intro x y hxy
      have hxy' := congrArg Subtype.val hxy
      simp only at hxy'
      ext
      exact hxy'
    have hK'c : Nat.card K' = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
    calc Nat.card K = Nat.card (K'.map θ) * Nat.card f.ker := by rw [← hK'c, h1]
      _ ≤ 4 * Nat.card ↥(K ⊓ C) := Nat.mul_le_mul hθK4 hker

theorem StrothFrame.IsD.mem_normalizer_omegaIn_of_cent (h : F.IsD D dD) (hτ : τ.m ≠ τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) → τ.m = τ.n)
    {r : ℕ} (hR : Nat.card ↥((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) ≤ r * Nat.card D)
    (hA : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G)) < Nat.card D)
    (hB : ∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∀ y ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), y ∉ D →
      4 * r * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
        Subgroup.centralizer ({y} : Set G)) < Nat.card D)
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
    by_contra hKR
    obtain ⟨⟨y, hyK, hyR⟩, hcount0⟩ := h.exists_mem_uv_mul_of_normal hk huvR hKN hKnorm hKc hKR
    have hcount : Nat.card K ≤ 4 * Nat.card ↥(K ⊓ C) := hcount0
    set x := dD.uv⁻¹ * y with hx_def
    have hxR : x ∈ R := ⟨N.mul_mem (N.inv_mem huvN) (hKN hyK),
      Subgroup.mem_centralizer_iff.mpr fun w hw => hyR w hw⟩
    have hyx : dD.uv * x = y := by rw [hx_def, mul_inv_cancel_left]
    have hKD : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) := by
      intro z hz
      refine ⟨hz.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ rfl
      rw [hyx]
      exact hKc _ hyK _ hz.1
    have hKCR : K ⊓ C = K ⊓ R := by
      ext z
      exact ⟨fun hz => ⟨hz.1, hKN hz.1, hz.2⟩, fun hz => ⟨hz.1, hz.2.2⟩⟩
    by_cases hcase : K ⊓ C ≤ D
    ·
      have h1 : Nat.card ↥(K ⊓ C) ≤ Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G)) :=
        Subgroup.card_le_of_le (fun z hz => hKD ⟨hz.1, hcase hz⟩)
      have h2 := hA x hxR
      omega
    ·
      obtain ⟨y₂, hy₂KC, hy₂D⟩ := SetLike.not_le_iff_exists.mp hcase
      have hy₂R : y₂ ∈ R := ⟨hKN hy₂KC.1, hy₂KC.2⟩
      have hKD2 : K ⊓ D ≤ D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({y₂} : Set G) := by
        intro z hz
        refine ⟨hKD hz, Subgroup.mem_centralizer_iff.mpr ?_⟩
        rintro _ rfl
        exact hKc _ hy₂KC.1 _ hz.1
      have hidx : Nat.card ↥(K ⊓ R) ≤ r * Nat.card ↥(K ⊓ D) := by
        have e1 := Subgroup.relIndex_mul_card (H := D) (K := K ⊓ R)
        have e2 := Subgroup.relIndex_mul_card (H := D) (K := R)
        have hDKR : D ⊓ (K ⊓ R) = K ⊓ D := by
          ext z
          exact ⟨fun hz => ⟨hz.2.1, hz.1⟩, fun hz => ⟨hz.2, hz.1, hDR hz.2⟩⟩
        have hDR' : D ⊓ R = D := inf_eq_left.mpr hDR
        rw [hDKR] at e1
        rw [hDR'] at e2
        have hne : D.relIndex R ≠ 0 := by
          intro h0
          rw [h0, zero_mul] at e2
          exact (Nat.card_pos (α := R)).ne' e2.symm
        have hle := Subgroup.relIndex_le_of_le_right (H := D) (inf_le_right : K ⊓ R ≤ R) hne
        have hpos : 0 < Nat.card D := Nat.card_pos
        have hrel : D.relIndex R ≤ r := by
          by_contra hlt
          push Not at hlt
          have : (r + 1) * Nat.card D ≤ D.relIndex R * Nat.card D :=
            Nat.mul_le_mul_right _ hlt
          nlinarith
        calc Nat.card ↥(K ⊓ R) = D.relIndex (K ⊓ R) * Nat.card ↥(K ⊓ D) := e1.symm
          _ ≤ r * Nat.card ↥(K ⊓ D) := Nat.mul_le_mul_right _ (hle.trans hrel)
      have h1 : Nat.card ↥(K ⊓ D) ≤ Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv * x} : Set G) ⊓
          Subgroup.centralizer ({y₂} : Set G)) := Subgroup.card_le_of_le hKD2
      have h2 := hB x hxR y₂ hy₂R hy₂D
      rw [hKCR] at hcount
      have h3 : Nat.card K ≤ 4 * (r * Nat.card ↥(K ⊓ D)) :=
        hcount.trans (Nat.mul_le_mul_left 4 hidx)
      have h4 : 4 * (r * Nat.card ↥(K ⊓ D)) ≤ 4 * r * Nat.card ↥(D ⊓
          Subgroup.centralizer ({dD.uv * x} : Set G) ⊓ Subgroup.centralizer ({y₂} : Set G)) := by
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

theorem inf_centralizer_mul_of_mem (hD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x)
    {b x : G} (hx : x ∈ D) :
    D ⊓ Subgroup.centralizer ({b * x} : Set G) = D ⊓ Subgroup.centralizer ({b} : Set G) := by
  ext d
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hd => ?_
  have hxd : x * d = d * x := hD _ hx _ hd
  constructor
  · intro h1
    refine mul_right_cancel (b := x) ?_
    calc d * b * x = d * (b * x) := by group
      _ = b * x * d := h1
      _ = b * d * x := by rw [mul_assoc, hxd, ← mul_assoc]
  · intro h1
    calc d * (b * x) = d * b * x := by group
      _ = b * d * x := by rw [h1]
      _ = b * x * d := by rw [mul_assoc, ← hxd, ← mul_assoc]

theorem StrothWeakTypeData.not_forall_commute_uv_of_torus (dD : StrothWeakTypeData D τ)
    {v : Torus τ.k} (hv : 2 • v = 0) (hφ : τ.action.φuv v ≠ v) :
    ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w := by
  intro hall
  set x : D := Additive.toMul (dD.e.symm v) with hx
  have hxe : dD.e (Additive.ofMul x) = v := by simp [hx]
  have hx2 : x * x = 1 := (mul_self_eq_one_iff_two_nsmul dD.e x).mpr (by rw [hxe]; exact hv)
  have hc := hall _ (mem_omegaIn_one_of_mul_self x.2 (congrArg Subtype.val hx2))
  have hconj : conjBy dD.uv_mem x = x := Subtype.ext (by
    change dD.uv⁻¹ * (x : G) * dD.uv = x
    rw [mul_assoc, hc, inv_mul_cancel_left])
  apply hφ
  rw [← hxe, ← dD.uv_conj, hconj]

theorem StrothFrame.IsD.mem_normalizer_omegaIn_of_R_eq (h : F.IsD D dD) (hτ : τ.m ≠ τ.n)
    (hk : ∀ i, 1 ≤ τ.k i) (huvR : ¬ ∀ w ∈ omegaIn 1 D, w * dD.uv = dD.uv * w)
    (h226 : ∀ B : Subgroup G, B ≤ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) →
      (∀ x ∈ (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
          Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G), ∀ b ∈ B,
        x * b * x⁻¹ ∈ B) →
      B ≠ D → (∃ g : G, B = D.map (MulAut.conj g).toMonoidHom) → τ.m = τ.n)
    (hRD : (F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) = D)
    (hA : 4 * Nat.card ↥(D ⊓ Subgroup.centralizer ({dD.uv} : Set G)) < Nat.card D) {g : G}
    (hgN : g ∈ Subgroup.normalizer
      (((F.S : Subgroup G) ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  have hcommD : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (dD.isMulCommutative.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine h.mem_normalizer_omegaIn_of_cent hτ hk huvR h226 (r := 1) (by rw [hRD, one_mul])
    (fun x hx => ?_) (fun x _ y hy hyD => absurd (hRD ▸ hy) hyD) hgN
  rw [hRD] at hx
  rw [inf_centralizer_mul_of_mem hcommD hx]
  exact hA

theorem StrothFrame.IsD.mem_normalizer_omegaIn_of_card_le (h : F.IsD D dD)
    (hD : Nat.card D ≤ 32) {g : G} (hg : g ∈ (F.S : Subgroup G)) :
    g ∈ Subgroup.normalizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  have hDA : F.A = D :=
    Subgroup.eq_of_le_of_card_ge h.A_le (by rw [F.dA.card_eq_32]; exact hD)
  have hCA : Subgroup.centralizer (F.A : Set G) ⊓ (F.S : Subgroup G) = F.A := by
    rw [inf_comm, hDA]
    exact h.cent
  have hgN := F.le_normalizer_A hCA hg
  rw [hDA] at hgN
  exact normalizer_le_normalizer_omegaIn D hgN

end Count

end CFSG.CGT.Stroth77
