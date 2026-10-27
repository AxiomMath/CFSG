module

public import CFSG.ClassicalInvolution.Asc77.AscS24BHCent
public import CFSG.ClassicalInvolution.Asc77.AscS24BHFrame
public import CFSG.ClassicalInvolution.Asc77.AscT7L4

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace S24B

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace HCtx

variable {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z u : G}
  (H : HCtx p f Ω K K' W S R R' z u)

theorem kPerp_J : KPerp Ω H.C.D.F.ρ₃.K = {H.C.D.F.ρ₃.K, H.Js} := by
  have hst := H.C.hs.stand
  have hΩ := hst.hyp
  obtain ⟨g, hg⟩ := hst.trans _ H.C.D.F.ρ₃.hK
  have h1 := T7L.kPerp_conj_pair hΩ.conjInvariant H.C.hs.perp g
  rw [hg] at h1
  have hTR : H.Ts ∈ RSet Ω := mem_RSet_of_isSylow2In H.Js_mem H.Ts_syl
  have h8 := hΩ.eight_le_of_mem_RSet hst.odd hTR
  have hTN := hΩ.le_normalizer_of_le_centralizer hst.odd hst.five H.C.D.F.ρ₃.hK H.Js_mem
    H.Js_ne.symm H.C.hjJ H.Ts_syl.1 H.Ts_syl.2.1 (by omega)
    (H.Ts_syl.1.trans (le_centralizer_of_unique H.hjJs))
  have hnbr : H.Js ∈ omegaNbr Ω H.C.D.F.ρ₃.K := ⟨H.Js_mem, H.Js_ne, H.Ts, hTR, H.Ts_syl.1, hTN⟩
  have hmem : H.Js ∈ KPerp Ω H.C.D.F.ρ₃.K := Set.mem_insert_of_mem _ hnbr
  rw [h1] at hmem
  rcases hmem with h | h
  · exact absurd h H.Js_ne
  · rw [h1, h]

theorem exists_L [IsSimpleGroup G] {u₁ : G} (hu : u₁ ∈ K ⊔ K') (hu1 : u₁ ≠ 1) (huz : u₁ ≠ z)
    (hu2 : u₁ * u₁ = 1) :
    ∃ L ∈ Ω, IsUniqueInvolution L u₁ ∧
      ∀ M ∈ KPerp Ω L, M ≤ Subgroup.centralizer ({H.a} : Set G) := by
  have hΩ := H.C.hs.stand.hyp
  obtain ⟨c, hc, hcu⟩ := T7K.exists_conj_of_involution H.C.hs H.C.j_mem_sup H.C.hjJ.ne_one
    H.C.z_ne_j.symm H.C.hjJ.sq hu hu1 huz hu2
  have hca : c * H.a = H.a * c :=
    Subgroup.mem_centralizer_singleton_iff.mp ((sup_le H.K_le H.K'_le) hc)
  refine ⟨conjSub c H.C.D.F.ρ₃.K, hΩ.conjInvariant c _ H.C.D.F.ρ₃.hK, ?_, ?_⟩
  · have h := H.C.hjJ.conj c
    rwa [hcu] at h
  · intro M hM
    rw [T7L.kPerp_conj_pair hΩ.conjInvariant H.kPerp_J c] at hM
    rcases hM with h | h <;> rw [h]
    · exact conjSub_le_centralizer H.J_le hca
    · exact conjSub_le_centralizer H.Js_le hca

include H in
theorem not_mem_K' {y : G} (hy : y ∈ K) (oy : orderOf y = 4) : y ∉ K' := by
  intro hy'
  have hΩ := H.C.hs.stand.hyp
  have h2 : IsPGroup 2 ↥(Subgroup.zpowers y) := T7A.isPGroup_zpowers_of_orderOf_four oy
  have h4 : 4 ≤ Nat.card ↥(Subgroup.zpowers y) := by rw [Nat.card_zpowers, oy]
  exact H.C.hs.hne (hΩ.eq_of_le_of_le H.C.hs.stand.mem H.C.hs.hK'.1 h2 h4
    (Subgroup.zpowers_le.mpr hy) (Subgroup.zpowers_le.mpr hy')).symm

theorem third_le [IsSimpleGroup G] {W₁ : Subgroup G} (c : Thompson.Ctx p f Ω W₁)
    {e : ↥(muGroup Ω W₁) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W₁ ↔ (e x).IsSwap) (F : T7E.Frame4 Ω W₁)
    (hFK : F.ρ.K = K) (hFK' : F.ρ'.K = K') (hFz : F.z = z)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) :
    F.ρ₃.r ∈ Subgroup.centralizer ({H.a} : Set G) := by
  have hst := H.C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ := hst.hyp
  obtain ⟨x₁, x₂, x₃, m, hm, h₁, h₂, h₃, o₁, o₂, o₃, z₁, z₂, z₃, k₁, k₂, k₃, -⟩ :=
    F.exists_structure c he hab hcomm hac
  have mx₁ : x₁ ∈ F.ρ.R ⊓ W₁ := h₁ ▸ Subgroup.mem_zpowers x₁
  have mx₂ : x₂ ∈ F.ρ'.R ⊓ W₁ := h₂ ▸ Subgroup.mem_zpowers x₂
  have ob : orderOf (x₁ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₁) (n := m) (by omega) (by rw [o₁]; exact dvd_mul_left m 4)
    rwa [o₁, Nat.mul_div_cancel _ hm] at this
  have ob' : orderOf (x₂ ^ m) = 4 := by
    have := orderOf_pow_of_dvd (x := x₂) (n := m) (by omega) (by rw [o₂]; exact dvd_mul_left m 4)
    rwa [o₂, Nat.mul_div_cancel _ hm] at this
  have hbK : x₁ ^ m ∈ F.ρ.K ⊓ W₁ := ⟨F.ρ.hRK.1 (F.ρ.R.pow_mem mx₁.1 m), W₁.pow_mem mx₁.2 m⟩
  have hb'K : x₂ ^ m ∈ F.ρ'.K ⊓ W₁ := ⟨F.ρ'.hRK.1 (F.ρ'.R.pow_mem mx₂.1 m), W₁.pow_mem mx₂.2 m⟩
  obtain ⟨u₁, hu₁, hsu, -⟩ := T7D.frame_fixed c F.ρ F.ρ' F.ρ₃ F.hnbr F.hnbr' F.hne₁ F.hne₂ F.hn₁
    F.hn₂ F.hn₁' F.hn₂' F.hz F.hz' F.hj hbK hb'K ob ob'
  have hbKK : x₁ ^ m ∈ K := hFK ▸ hbK.1
  have hb'KK : x₂ ^ m ∈ K' := hFK' ▸ hb'K.1
  have hbb : x₁ ^ m * x₁ ^ m = z := hFz ▸ T7A.sq_eq_of_orderOf_four F.hz hbK.1 ob
  have hb'b' : x₂ ^ m * x₂ ^ m = z := hFz ▸ T7A.sq_eq_of_orderOf_four F.hz' hb'K.1 ob'
  have hcomm₁₂ : x₁ ^ m * x₂ ^ m = x₂ ^ m * x₁ ^ m := c.comm_W _ hbK.2 _ hb'K.2
  obtain ⟨y, hyK, hyW, hyy, hyc, rfl⟩ : ∃ y, y ∈ K ∧ y ∈ W₁ ∧ y * y = z ∧
      y * x₂ ^ m = x₂ ^ m * y ∧ u₁ = y * x₂ ^ m := by
    rcases hu₁ with h | h
    · exact ⟨x₁ ^ m, hbKK, hbK.2, hbb, hcomm₁₂, h⟩
    · refine ⟨(x₁ ^ m)⁻¹, K.inv_mem hbKK, W₁.inv_mem hbK.2, ?_, ?_, h⟩
      · rw [← mul_inv_rev, hbb]; exact inv_eq_of_mul_eq_one_right H.C.hzK.sq
      · exact (Commute.inv_left hcomm₁₂).eq
  have hu2 : y * x₂ ^ m * (y * x₂ ^ m) = 1 := by
    calc y * x₂ ^ m * (y * x₂ ^ m) = y * (x₂ ^ m * y) * x₂ ^ m := by group
      _ = y * (y * x₂ ^ m) * x₂ ^ m := by rw [hyc]
      _ = (y * y) * (x₂ ^ m * x₂ ^ m) := by group
      _ = 1 := by rw [hyy, hb'b', H.C.hzK.sq]
  have hnot : ∀ v ∈ K, y * x₂ ^ m ≠ v := by
    intro v hv h
    have e : x₂ ^ m = y⁻¹ * v := by rw [← h]; group
    have hK : x₂ ^ m ∈ K := by rw [e]; exact K.mul_mem (K.inv_mem hyK) hv
    exact H.not_mem_K' hK ob' hb'KK
  obtain ⟨L, hLΩ, hLu, hLperp⟩ := H.exists_L (Subgroup.mul_mem _ (Subgroup.mem_sup_left hyK)
    (Subgroup.mem_sup_right hb'KK)) (hnot 1 K.one_mem) (hnot z H.C.hzK.mem) hu2
  have hT : F.ρ₃.R ≤ Subgroup.centralizer ({y * x₂ ^ m} : Set G) := by
    have huW : y * x₂ ^ m ∈ W₁ := W₁.mul_mem hyW hb'K.2
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hxW : x ∈ W₁
    · exact c.comm_W x hxW _ huW
    · have h1 := Thompson.D_inv_mul_mem c.hp c.hq c.hΩ c.hW F.ρ₃.hR F.ρ₃.hr hx F.ρ₃.hrW hxW
      have h2 : F.ρ₃.r⁻¹ * x * (y * x₂ ^ m) = (y * x₂ ^ m) * (F.ρ₃.r⁻¹ * x) := c.comm_W _ h1 _ huW
      have hs : F.ρ₃.r * (y * x₂ ^ m) = (y * x₂ ^ m) * F.ρ₃.r := by
        calc F.ρ₃.r * (y * x₂ ^ m) = F.ρ₃.r * (y * x₂ ^ m) * F.ρ₃.r⁻¹ * F.ρ₃.r := by group
          _ = (y * x₂ ^ m) * F.ρ₃.r := by rw [hsu]
      calc x * (y * x₂ ^ m) = F.ρ₃.r * (F.ρ₃.r⁻¹ * x * (y * x₂ ^ m)) := by group
        _ = F.ρ₃.r * ((y * x₂ ^ m) * (F.ρ₃.r⁻¹ * x)) := by rw [h2]
        _ = (F.ρ₃.r * (y * x₂ ^ m)) * (F.ρ₃.r⁻¹ * x) := by group
        _ = ((y * x₂ ^ m) * F.ρ₃.r) * (F.ρ₃.r⁻¹ * x) := by rw [hs]
        _ = (y * x₂ ^ m) * x := by group
  have hJ₁ : F.ρ₃.K ∈ KPerp Ω L := by
    by_cases hJL : F.ρ₃.K = L
    · rw [hJL]; exact Set.mem_insert _ _
    · have h8 := hΩ.eight_le_of_mem_RSet hp F.ρ₃.hR.1
      have hN := hΩ.le_normalizer_of_le_centralizer hp hq hLΩ F.ρ₃.hK (Ne.symm hJL) hLu
        F.ρ₃.hRK.1 F.ρ₃.hRK.2.1 (by omega) hT
      exact Set.mem_insert_of_mem _ ⟨F.ρ₃.hK, hJL, F.ρ₃.R, F.ρ₃.hR.1, F.ρ₃.hRK.1, hN⟩
  exact hLperp _ hJ₁ (F.ρ₃.hRK.1 F.ρ₃.hr)

theorem exists_conj_K' [IsSimpleGroup G] :
    ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = K' := by
  have hs : H.C.D.F.ρ₃.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    H.J_le (H.C.D.F.ρ₃.hRK.1 H.C.D.F.ρ₃.hr)
  have hr : H.C.D.F.ρ.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr H.comm_r
  have ht : H.C.D.F.ρ'.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr H.comm_t
  obtain ⟨h, hh, hK⟩ := exists_conj_of_frame H.C.D.c H.C.D.hφ H.C.D.F H.C.D.hab H.C.D.hcomm
    H.C.D.hac hr ht hs H.C.D.F.ρ'
  exact ⟨h, hh, (congrArg (conjSub h) H.C.hK).symm.trans (hK.trans H.C.hK')⟩

theorem key [IsSimpleGroup G] (W₁ : Subgroup G) (hW₁ : W₁ ∈ WSet Ω) (hzW₁ : z ∈ W₁)
    (J' : Subgroup G) (hJ' : J' ∈ Ω) (hT : ∃ T ∈ DSet Ω W₁, IsSylow2In T J') :
    ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J' := by
  obtain ⟨T, hTD, hTJ'⟩ := hT
  have hst := H.C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ := hst.hyp
  have c : Thompson.Ctx p f Ω W₁ := T7D.ctx_of_stand hst hW₁
  obtain ⟨S₁, ρ, ρ', -, hρK, hρ'K, -, -, hnbr, hnbr', hab, hcomm⟩ :=
    T7E.exists_twin_reps H.C.hs hW₁ hzW₁
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep hp hq hΩ hW₁ hJ' hTJ' hTD
  rcases T7E.rep_dichotomy H.C.hs hW₁ ρ ρ' hab hcomm with hall | ⟨e, he, σ₃, hac, hbc⟩
  · rcases hall σ with h | h
    · exact ⟨1, Subgroup.one_mem _, by rw [conjSub_one, ← hσK, h, hρK]⟩
    · obtain ⟨g, hg, hgK⟩ := H.exists_conj_K'
      exact ⟨g, hg, by rw [hgK, ← hσK, h, hρ'K]⟩
  · obtain ⟨F, hFρ, hFρ', hFρ₃, hFz⟩ :=
      T7E.frame4_of_twin_reps H.C.hs hW₁ hρK hρ'K hnbr hnbr' hac hbc
    subst hFρ hFρ' hFρ₃
    have hs₁ := H.third_le c he F hρK hρ'K hFz hab hcomm hac
    have hr₁ : F.ρ.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
      H.K_le (hρK ▸ F.ρ.hRK.1 F.ρ.hr)
    have hr₁' : F.ρ'.r ∈ Subgroup.centralizer ({H.a} : Set G) :=
      H.K'_le (hρ'K ▸ F.ρ'.hRK.1 F.ρ'.hr)
    obtain ⟨h, hh, hK⟩ := exists_conj_of_frame c he F hab hcomm hac hr₁ hr₁' hs₁ σ
    exact ⟨h, hh, by rw [← hρK, hK, hσK]⟩

theorem trans [IsSimpleGroup G] :
    ∀ J ∈ dstarComp Ω K, ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J := by
  have hst := H.C.hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have step : ∀ J' : Subgroup G, dstarAdj Ω K J' →
      ∃ h ∈ Subgroup.centralizer ({H.a} : Set G), conjSub h K = J' := by
    rintro J' ⟨hJ'Ω, hadj⟩
    rcases hadj with h | h
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁K, hTJ'⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hp hq hΩ hK h
      have hzW₁ : z ∈ W₁ :=
        (Thompson.uniqueInvolution_mem_W hp hq hΩ hW₁ hK hR₁ hR₁K H.C.hzK).2
      exact H.key W₁ hW₁ hzW₁ J' hJ'Ω ⟨T, hT, hTJ'⟩
    · obtain ⟨W₁, hW₁, R₁, hR₁, T, hT, hR₁J', hTK⟩ :=
        Thompson.exists_W_of_mem_omegaStarNbr hp hq hΩ hJ'Ω h
      have hzW₁ : z ∈ W₁ := (Thompson.uniqueInvolution_mem_W hp hq hΩ hW₁ hK hT hTK H.C.hzK).2
      exact H.key W₁ hW₁ hzW₁ J' hJ'Ω ⟨R₁, hR₁, hR₁J'⟩
  intro J hJ
  have hJ' : Relation.ReflTransGen (dstarAdj Ω) K J := hJ
  clear hJ
  induction hJ' with
  | refl => exact ⟨1, Subgroup.one_mem _, conjSub_one K⟩
  | @tail J₁ J₂ _ hadj ih =>
    obtain ⟨h₁, hh₁, hJ₁⟩ := ih
    have hadj' : dstarAdj Ω K (conjSub h₁⁻¹ J₂) := by
      obtain ⟨hJ₂, h | h⟩ := hadj
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inl ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
      · refine ⟨hΩ.conjInvariant h₁⁻¹ J₂ hJ₂, Or.inr ?_⟩
        have := omegaStarNbr_conj hΩ.conjInvariant h h₁⁻¹
        rwa [← hJ₁, conjSub_inv_conjSub] at this
    obtain ⟨h₂, hh₂, hJ₂⟩ := step _ hadj'
    refine ⟨h₁ * h₂, Subgroup.mul_mem _ hh₁ hh₂, ?_⟩
    rw [conjSub_mul, hJ₂, conjSub_conjSub_inv]

end HCtx

end S24B

end CFSG.ClassicalInvolution.Asc77
