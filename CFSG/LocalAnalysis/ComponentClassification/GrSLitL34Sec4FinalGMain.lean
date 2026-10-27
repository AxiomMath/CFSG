module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FinalGR
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndG

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem false_of_transfer_simple (hG : IsSimpleGroup G) (hnab : ∃ g h : G, g * h ≠ h * g)
    {S Q : Subgroup G} (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hQS : Q ≤ S)
    (hQidx : Q.relIndex S = 2) {u : G} (hu : orderOf u = 2) (hQu : ∀ g : G, g⁻¹ * u * g ∉ Q) :
    False := by
  obtain ⟨P, rfl⟩ := hS
  obtain ⟨N, -, hNn, hsq, huN⟩ := Quasithin.thompson_transfer_exists_normal_subgroup
    (X := ⊤) le_top P.isPGroup' (by rw [relIndex_top_right]; exact P.not_dvd_index) hQS hQidx
    (mem_top u) hu (fun x _ => hQu x)
  have hN : N.Normal :=
    normalizer_eq_top_iff.mp (top_le_iff.mp ((normal_subgroupOf_iff_le_normalizer le_top).mp hNn))
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · obtain ⟨g, h, hgh⟩ := hnab
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (by
      have := hsq x (mem_top x)
      rwa [hbot, mem_bot, pow_two] at this)
    apply hgh
    calc g * h = (g * h)⁻¹ := (hinv _).symm
      _ = h * g := by rw [mul_inv_rev, hinv, hinv]
  · exact huN (htop ▸ mem_top u)

omit [Finite G] in
theorem isEightGroup_map_conj {E : Subgroup G} (hE : IsEightGroup E) (g : G) :
    IsEightGroup (E.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group, hE.1.1 x hx y hy]
    group
  · rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, hE.1.2 x hx]
    group
  · rw [card_map_of_injective (MulAut.conj g).injective, hE.2]

namespace Data

variable (D : Data G)

theorem R_le_P₁ : D.R ≤ D.P₁ := le_inf (fun _ h => h.1) D.R_le_L₁

theorem relIndex_R_P₁ : D.R.relIndex D.P₁ = 2 := by
  have h := relIndex_mul_card D.R D.P₁
  rw [inf_eq_left.mpr D.R_le_P₁, D.card_R, D.card_P₁] at h
  omega

theorem conj_a_of_mem_P₁ {u : G} (hu : u ∈ D.P₁) (hu2 : orderOf u = 2) :
    ∃ g : G, u = g⁻¹ * D.a * g := by
  by_contra hna
  have huu : u * u = 1 := by rw [← pow_two, ← hu2, pow_orderOf_eq_one]
  have hidx : ¬ 2 ∣ D.P₁.relIndex D.L₁ := by
    obtain ⟨-, Q, hQ⟩ := D.sylow_P₁
    have := Q.not_dvd_index
    rw [hQ] at this
    exact this
  obtain ⟨N, -, -, hsq, huN⟩ := Quasithin.thompson_transfer_exists_normal_subgroup D.P₁_le_L₁
    (D.isPGroup_S.to_le D.P₁_le_S) hidx D.R_le_P₁ D.relIndex_R_P₁ (D.P₁_le_L₁ hu) hu2
    (fun x hx hmem => by
      have h1 : (x⁻¹ * u * x) * (x⁻¹ * u * x) = 1 := by
        rw [show x⁻¹ * u * x * (x⁻¹ * u * x) = x⁻¹ * (u * u) * x by group, huu]
        group
      have h2 : x⁻¹ * u * x ≠ 1 := by
        intro h
        have hu1 : u = 1 := by
          calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
            _ = 1 := by rw [h]; group
        rw [hu1, orderOf_one] at hu2
        exact absurd hu2 (by norm_num)
      obtain ⟨g, hg⟩ := D.cls _ hmem h1 h2
      exact hna ⟨g * x⁻¹, by
        calc u = x * (x⁻¹ * u * x) * x⁻¹ := by group
          _ = (g * x⁻¹)⁻¹ * D.a * (g * x⁻¹) := by rw [hg]; group⟩)
  exact huN (oddGen_le_of_sq (fun y hy => hsq y hy) (D.P₁_le_L₁ hu))

theorem Seven.conj_a {D : Data G} (H : D.Seven) : ∃ g : G, H.c' = g⁻¹ * D.a * g := by
  by_contra hna
  refine false_of_transfer_simple D.simple D.nab D.sylow D.P₁_le_S D.relIndex_P₁ H.orderOf_c'
    fun g hg => ?_
  have hord : orderOf (g⁻¹ * H.c' * g) = 2 := by
    rw [show g⁻¹ * H.c' * g = g⁻¹ * H.c' * g⁻¹⁻¹ by rw [inv_inv], orderOf_conj_eq]
    exact H.orderOf_c'
  obtain ⟨k, hk⟩ := D.conj_a_of_mem_P₁ hg hord
  exact hna ⟨k * g⁻¹, by
    calc H.c' = g * (g⁻¹ * H.c' * g) * g⁻¹ := by group
      _ = (k * g⁻¹)⁻¹ * D.a * (k * g⁻¹) := by rw [hk]; group⟩

theorem N_le_N_kernel : normalizer (D.J : Set G) ≤ normalizer (coreActionKernel D.J : Set G) :=
  fun _ hn => GrS4.mem_normalizer_of_map_le_self (by
    rintro _ ⟨q, hq, rfl⟩
    exact conj_mem_coreActionKernel hn hq)

theorem not_isEightGroup_le_kernel {E : Subgroup G} (hE : IsEightGroup E)
    (hEK : E ≤ coreActionKernel D.J) : False := by
  have hSK : IsSylowTwoIn (D.S ⊓ coreActionKernel D.J) (coreActionKernel D.J) :=
    GrS4.isSylowTwoIn_inf_of_normal D.sylowNJ (fun q hq => (mem_coreActionKernel.mp hq).1)
      D.N_le_N_kernel
  have hE2 : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hE.2]; norm_num)
  obtain ⟨k, -, hk⟩ := GrS4.exists_conj_mem_of_isSylowTwoIn hSK hEK hE2
  refine false_of_isEightGroup_le (isEightGroup_map_conj hE k⁻¹) D.kernel_cyclic ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  exact hk y hy

include D in
theorem false_of_noFrobenius (hNo : L34NoFrobeniusFact) : False := by
  obtain ⟨H⟩ := D.nonempty_seven
  obtain ⟨g, hg⟩ := H.conj_a
  have hac : D.a = g * H.c' * g⁻¹ := by rw [hg]; group
  have hc'B : ∀ b ∈ D.B, b * H.c' = H.c' * b :=
    fun b hb => mem_centralizer_iff.mp (D.T_le_C H.c'_mem) b hb
  set h' := g * H.h * g⁻¹ with hh'
  set B' := D.B.map (MulAut.conj g).toMonoidHom with hB'
  have hconj : ∀ {y : G}, y ∈ B' ↔ g⁻¹ * y * g ∈ D.B := by
    intro y
    constructor
    · rintro ⟨b, hb, rfl⟩
      show g⁻¹ * (g * b * g⁻¹) * g ∈ D.B
      rwa [show g⁻¹ * (g * b * g⁻¹) * g = b by group]
    · intro hy
      refine ⟨g⁻¹ * y * g, hy, ?_⟩
      show g * (g⁻¹ * y * g) * g⁻¹ = y
      group
  have hh'a : h' ∈ centralizer ({D.a} : Set G) := by
    rw [mem_centralizer_singleton_iff, hac, hh']
    calc g * H.h * g⁻¹ * (g * H.c' * g⁻¹) = g * (H.h * H.c') * g⁻¹ := by group
      _ = g * H.c' * g⁻¹ * (g * H.h * g⁻¹) := by rw [H.c'_comm]; group
  have hB'a : B' ≤ centralizer ({D.a} : Set G) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff, hac]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * b * g⁻¹ * (g * H.c' * g⁻¹) = g * (b * H.c') * g⁻¹ := by group
      _ = g * H.c' * g⁻¹ * (g * b * g⁻¹) := by rw [hc'B b hb]; group
  have hh'N : h' ∈ normalizer (D.J : Set G) := D.centralizer_le hh'a
  have hB'N : B' ≤ normalizer (D.J : Set G) := hB'a.trans D.centralizer_le
  have hB'8 : IsEightGroup B' := isEightGroup_map_conj D.eight g
  have hh'B' : h' ∈ normalizer (B' : Set G) := GrS4.mem_normalizer_of_map_le_self (by
    rintro _ ⟨e, he, rfl⟩
    have he' : g⁻¹ * e * g ∈ D.B := hconj.mp he
    have := (mem_normalizer_iff.mp (D.L_le_N_B H.h_mem) _).mp he'
    refine hconj.mpr ?_
    show g⁻¹ * (h' * e * h'⁻¹) * g ∈ D.B
    rwa [hh', show g⁻¹ * (g * H.h * g⁻¹ * e * (g * H.h * g⁻¹)⁻¹) * g =
      H.h * (g⁻¹ * e * g) * H.h⁻¹ by group])
  have hfix' : ∀ e ∈ B', h' * e = e * h' → e = 1 := by
    intro e he hhe
    rw [hconj] at he
    have hb : g⁻¹ * e * g ∈ D.B ⊓ centralizer ({H.h} : Set G) := by
      refine mem_inf.mpr ⟨he, mem_centralizer_singleton_iff.mpr ?_⟩
      calc g⁻¹ * e * g * H.h = g⁻¹ * (e * (g * H.h * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * H.h * g⁻¹) * e) * g := by rw [← hhe]
        _ = H.h * (g⁻¹ * e * g) := by group
    rw [H.inf_centralizer_B, mem_bot] at hb
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [hb]; group
  have hpow' : h' ^ 7 ^ H.e = 1 := by
    rw [hh', conj_pow, H.h_pow]
    group
  have hK : B' ⊓ coreActionKernel D.J = ⊥ := by
    have hD : h' ∈ normalizer ((B' ⊓ coreActionKernel D.J : Subgroup G) : Set G) :=
      GrS4.inf_mem_normalizer hh'B' (D.N_le_N_kernel hh'N)
    have hdvd : Nat.card ↥(B' ⊓ coreActionKernel D.J) ∣ 8 := by
      rw [← hB'8.2]
      exact card_dvd_of_le inf_le_left
    have hfixD : B' ⊓ coreActionKernel D.J ⊓ centralizer ({h'} : Set G) = ⊥ := by
      refine eq_bot_iff.mpr fun e he => ?_
      obtain ⟨⟨heB, -⟩, heC⟩ := mem_inf.mp he
      exact (mem_bot).mpr (hfix' e heB (mem_centralizer_singleton_iff.mp heC).symm)
    rcases card_eq_one_or_eight hpow' hD hdvd hfixD with h1 | h8
    · exact card_eq_one.mp h1
    · exfalso
      have heq : B' ⊓ coreActionKernel D.J = B' :=
        eq_of_le_of_card_ge inf_le_left (by rw [h8, hB'8.2])
      exact D.not_isEightGroup_le_kernel hB'8 (heq ▸ inf_le_right)
  obtain ⟨e, he, he1, hhe⟩ := hNo G D.J B' h' D.perfect D.l34 hB'N hB'8 hK hh'N hh'B'
  exact he1 (hfix' e he hhe)

end Data

theorem l34GraphFinalStep_of_inputs (hSol : SolomonFixedLayerStep)
    (hSq : L34OutSquareFact) (hNo : L34NoFrobeniusFact) : L34GraphFinalStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hZc hZ4 hQc hinv hSyl hcls B hBP hB8 hBZ hSN hBiff
    hAut c hcS hcc hcW hTc hiso hΩ hinvc hNS₀ hNB hφ
  obtain ⟨hbase, hU3, hL34, hmax, hS, -, -⟩ := hset
  obtain ⟨hsimple, hnab, -, -, -, -, -, -⟩ := id hbase
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have : IsSimpleGroup G := hsimple
  have hJper : ⁅J, J⁆ = J := UnbalancedCorr.commutator_eq_of_isPComponent hJa hJc
  have hZJle : zStarIn J ≤ J := map_subtype_le _
  have hZP : S ⊓ J ⊓ zStarIn J = S ⊓ zStarIn J := by rw [inf_assoc, inf_eq_right.mpr hZJle]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  exact Data.false_of_noFrobenius
    { a := a, c := c, J := J, S := S, B := B, simple := hsimple, nab := hnab
      centralizer_le :=
        GrS4.centralizer_le_normalizer_of_solomon hSol hbase ha2 hJa hJc hmax hL34
      perfect := hJper, l34 := hL34, sylow := hSyl, sylowNJ := hS, S_le_NB := hSN
      a_cent := hcent, a_ne := ha1, B_le := hBP, eight := hB8, BZ := hBZ, biff := hBiff
      aut := hAut, cls := hcls, c_mem := hcS, c_sq := hcc, c_not_mem := hcW, T_eq := hTc
      T₁_iso := hiso, T₁_omega := hΩ, T₁_inv := hinvc, N_T₁ := hNS₀, N_B := hNB, phi := hφ
      card_R := GrS4.card_sylow_eq hL34 (GrS4.isSylowTwoIn_inf hS) (by rwa [hZP])
      kernel_cyclic := hQc
      sq_mem := fun s hs => hSq G J hJper hL34 s (hS.1 hs)
        ((GrS4.isPGroup_of_isSylowTwoIn hS).to_le (zpowers_le.mpr hs)) } hNo

end CFSG.ComponentClassification.GrSLit.FinalG
