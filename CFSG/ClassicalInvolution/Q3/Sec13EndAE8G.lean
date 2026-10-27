module

public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8A
public import CFSG.ClassicalInvolution.Q3.Sec13EndAE8F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinMuLayer
import CFSG.ClassicalInvolution.Q3.Sec13EndDETwin

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace End18

variable {Ω : Set (Subgroup G)}

structure WFrame (Ω : Set (Subgroup G)) (W K : Subgroup G) (s g₀ : G) : Prop where
  hW : W ∈ WSet Ω
  hK : K ∈ Ω
  hs : s ∈ zGroup Ω
  hsK : conjSub s K ≠ K
  hV : twinSet Ω K ⊆ DSet Ω W
  hg₀ : g₀ ∈ K ⊓ W
  hg₀4 : orderOf g₀ = 4

theorem exists_wFrame (H : Hyp Ω) :
    ∃ (W K J : Subgroup G) (s g₀ : G), J ∈ Ω ∧ IsUniqueInvolution J s ∧ WFrame Ω W K s g₀ := by
  obtain ⟨K, hK, -, -, -⟩ := H.endHyp.exists_ne
  obtain ⟨J, hJ, s, hJs, hsK⟩ := H.exists_swap hK
  obtain ⟨W, hW, hV⟩ := H.exists_wSet_through hK
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution hK
  have hKD : K ∈ DSet Ω W := hV ⟨hK, z, hz, hz⟩
  obtain ⟨g₀, hg₀, hg₄⟩ := Q3T8.Asc77.Thompson.exists_orderOf_four H.endHyp.thmD.hyp hW hKD
  exact ⟨W, K, J, s, g₀, hJ, hJs,
    ⟨hW, hK, Subgroup.subset_closure ⟨J, hJ, hJs⟩, hsK, hV, hg₀, hg₄⟩⟩

namespace WFrame

variable {W K : Subgroup G} {s g₀ : G}

private theorem ae8ga_sq_eq_one_of_mem_zpowers {z x : G} (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hx : x ∈ Subgroup.zpowers z) : x * x = 1 := by
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hxo : orderOf x ∣ orderOf z := orderOf_dvd_of_mem_zpowers hx
  have h : x ^ orderOf z = 1 := orderOf_dvd_iff_pow_eq_one.mp hxo
  rw [hzo, pow_two] at h
  exact h

private theorem ae8ga_q8 {Ω : Set (Subgroup G)} (h : EndHyp Ω) {J : Subgroup G} (hJ : J ∈ Ω)
    {z : G} (hz : IsUniqueInvolution J z) : ∃ i j : G, Q8Data J z i j := by
  obtain ⟨i, j, hi, hj, hii, hjj, hji, hNF⟩ :=
    exists_q8_gen hz (h.isQuatSub_of_mem hJ) (h.card_eq_eight hJ)
  exact ⟨i, j, hz, hi, hj, hii, hjj, hji, hNF⟩

private theorem ae8ga_mem_zpowers_of_central {Ω : Set (Subgroup G)} (h : EndHyp Ω)
    {J : Subgroup G} (hJ : J ∈ Ω) {z x : G} (hz : IsUniqueInvolution J z) (hxJ : x ∈ J)
    (hc : ∀ y ∈ J, x * y = y * x) : x ∈ Subgroup.zpowers z := by
  by_contra hxz
  obtain ⟨i, j, hQ⟩ := ae8ga_q8 h hJ hz
  obtain ⟨w, hw, hne⟩ := det_tw_q8_noncomm hQ hxJ hxz
  exact hne (hc w hw)

private theorem ae8ga_twinSet_eq {Ω : Set (Subgroup G)} {K K' : Subgroup G}
    (h : K' ∈ twinSet Ω K) : twinSet Ω K' = twinSet Ω K := by
  obtain ⟨_, z, hzK, hzK'⟩ := h
  ext J
  constructor
  · rintro ⟨hJ, z', hz'K', hz'J⟩
    have hzz : z = z' := hzK'.eq hz'K'
    refine ⟨hJ, z, hzK, ?_⟩
    rw [hzz]
    exact hz'J
  · rintro ⟨hJ, z', hz'K, hz'J⟩
    have hzz : z = z' := hzK.eq hz'K
    refine ⟨hJ, z, hzK', ?_⟩
    rw [hzz]
    exact hz'J

private theorem ae8ga_exists_noncomm_pair {M : Type} [Group M] {S : Set M}
    (ψ : ↥(Subgroup.closure S) ≃* Equiv.Perm (Fin 4))
    (hψ : ∀ (x : M) (hx : x ∈ Subgroup.closure S), x ∈ S ↔ (ψ ⟨x, hx⟩).IsSwap) :
    ∃ x₁ ∈ S, ∃ x₂ ∈ S, x₁ * x₂ ≠ x₂ * x₁ := by
  set p₁ := ψ.symm (Equiv.swap (0 : Fin 4) 1) with hp₁
  set p₂ := ψ.symm (Equiv.swap (1 : Fin 4) 2) with hp₂
  have e1 : ψ p₁ = Equiv.swap 0 1 := ψ.apply_symm_apply _
  have e2 : ψ p₂ = Equiv.swap 1 2 := ψ.apply_symm_apply _
  have hs₁ : (ψ ⟨(p₁ : M), p₁.2⟩).IsSwap := by
    rw [show (⟨(p₁ : M), p₁.2⟩ : ↥(Subgroup.closure S)) = p₁ from rfl, e1]
    exact ⟨0, 1, by decide, rfl⟩
  have hs₂ : (ψ ⟨(p₂ : M), p₂.2⟩).IsSwap := by
    rw [show (⟨(p₂ : M), p₂.2⟩ : ↥(Subgroup.closure S)) = p₂ from rfl, e2]
    exact ⟨1, 2, by decide, rfl⟩
  refine ⟨p₁, (hψ _ p₁.2).mpr hs₁, p₂, (hψ _ p₂.2).mpr hs₂, fun heq => ?_⟩
  have hp : p₁ * p₂ = p₂ * p₁ := Subtype.ext heq
  have h12 : (Equiv.swap (0 : Fin 4) 1) * Equiv.swap 1 2 ≠ Equiv.swap 1 2 * Equiv.swap 0 1 := by
    decide
  apply h12
  have := congrArg ψ hp
  rw [map_mul, map_mul, e1, e2] at this
  exact this

private theorem ae8ga_isSylow2_self {Ω : Set (Subgroup G)} (h2 : ∀ J ∈ Ω, IsPGroup 2 ↥J)
    {K : Subgroup G} (hK : K ∈ Ω) : IsSylow2In K K :=
  ⟨le_rfl, h2 K hK, fun _ hVK _ hKV => le_antisymm hVK hKV⟩

private def ae8ga_repOf {Ω : Set (Subgroup G)} (h : EndHyp Ω) {W R : Subgroup G}
    (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) (hrW : r ∉ W) : Asc77.Thompson.Rep Ω W :=
  ⟨R, R, r, (h.mem_dSet_iff.mp hR).1, hR,
    ae8ga_isSylow2_self h.thmD.two (h.mem_dSet_iff.mp hR).1, hr, hrW⟩

private noncomputable def ae8ga_rep {Ω : Set (Subgroup G)} (h : EndHyp Ω) {W R : Subgroup G}
    (hW : W ∈ WSet Ω) (hR : R ∈ DSet Ω W) : Asc77.Thompson.Rep Ω W :=
  ae8ga_repOf h hR (Q3CL.Thompson.exists_not_mem_of_mem_D h.thmD.hyp hW hR).choose_spec.1
    (Q3CL.Thompson.exists_not_mem_of_mem_D h.thmD.hyp hW hR).choose_spec.2

private theorem ae8ga_mem_kperp_iff {Ω : Set (Subgroup G)} {R T : Subgroup G} :
    T ∈ KPerp Ω R ↔ T = R ∨ T ∈ omegaNbr Ω R :=
  Iff.rfl

private theorem ae8ga_ncard_eq {Ω : Set (Subgroup G)} (h : EndHyp Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) (ρ : Asc77.Thompson.Rep Ω W)
    (hρ : ρ.K = R) :
    (KPerp Ω R ∩ DSet Ω W).ncard =
      (Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρ)).ncard := by
  have hP : Q3CL.PartIHypG Ω := ⟨h.thmD.hyp, h.cls, h.thmD.aEmpty⟩
  have hrep : ∀ T ∈ DSet Ω W, ∃ σ : Asc77.Thompson.Rep Ω W, σ.K = T :=
    fun T hT => ⟨ae8ga_rep h hW hT, rfl⟩
  have : Nonempty (Asc77.Thompson.Rep Ω W) := ⟨ρ⟩
  choose! rep hrep using hrep
  obtain ⟨f, hf⟩ : ∃ f : Subgroup G → ↥(muGroup Ω W),
      ∀ T, f T = MuTab.muTabElt (rep T) := ⟨_, fun _ => rfl⟩
  have hRρ : MuTab.muTabElt (rep R) = MuTab.muTabElt ρ :=
    (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mpr (by rw [hrep R hR, hρ])
  have hfR : f R = MuTab.muTabElt ρ := by rw [hf, hRρ]
  have hinj : Set.InjOn f (KPerp Ω R ∩ DSet Ω W) := by
    intro T hT T' hT' hTT'
    rw [hf, hf] at hTT'
    have e := (Q3T6.Mu.muTabElt_eq_iff hP hW (rep T) (rep T')).mp hTT'
    rw [hrep T hT.2, hrep T' hT'.2] at e
    exact e
  have himg : f '' (KPerp Ω R ∩ DSet Ω W) =
      Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρ) := by
    ext x
    constructor
    · rintro ⟨T, ⟨hTp, hTD⟩, rfl⟩
      refine ⟨by rw [hf]; exact MuTab.muTabElt_mem (rep T), ?_⟩
      rw [← hfR]
      by_cases hTR : T = R
      · rw [hTR]
      · have hTn : T ∈ omegaNbr Ω R := (ae8ga_mem_kperp_iff.mp hTp).resolve_left hTR
        have hne : (rep R).K ≠ (rep T).K := by
          rw [hrep R hR, hrep T hTD]
          exact fun e => hTR e.symm
        have hc : MuTab.muTabElt (rep R) * MuTab.muTabElt (rep T) =
            MuTab.muTabElt (rep T) * MuTab.muTabElt (rep R) :=
          (Q3T6.Mu.muTab_commute_iff hP hW (rep R) (rep T) hne).mpr
            (by rw [hrep R hR, hrep T hTD]; exact hTn)
        rw [hf, hf]
        exact hc.symm
    · rintro ⟨hxΔ, hx⟩
      obtain ⟨σ, rfl⟩ := MuTab.exists_rep_of_mem_muDelta hxΔ
      have hσD : σ.K ∈ DSet Ω W := by
        have hRK : σ.R = σ.K :=
          (σ.hRK.2.2 σ.K le_rfl (h.thmD.two σ.K σ.hK) σ.hRK.1).symm
        rw [← hRK]
        exact σ.hR
      refine ⟨σ.K, ⟨?_, hσD⟩, ?_⟩
      · by_cases hσR : σ.K = R
        · exact ae8ga_mem_kperp_iff.mpr (Or.inl hσR)
        · refine ae8ga_mem_kperp_iff.mpr (Or.inr ?_)
          have hne : (rep R).K ≠ σ.K := by
            rw [hrep R hR]
            exact fun e => hσR e.symm
          have hcomm : MuTab.muTabElt (rep R) * MuTab.muTabElt σ =
              MuTab.muTabElt σ * MuTab.muTabElt (rep R) := by
            rw [hRρ]
            exact hx.symm
          have := (Q3T6.Mu.muTab_commute_iff hP hW (rep R) σ hne).mp hcomm
          rw [hrep R hR] at this
          exact this
      · rw [hf]
        exact (Q3T6.Mu.muTabElt_eq_iff hP hW _ _).mpr (hrep σ.K hσD)
  rw [← himg]
  exact hinj.ncard_image.symm

private theorem ae8ga_involution_mem {Ω : Set (Subgroup G)} (h : EndHyp Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {K : Subgroup G} (hK : K ∈ DSet Ω W) {z : G}
    (hz : IsUniqueInvolution K z) : z ∈ W := by
  have hKΩ : K ∈ Ω := (h.mem_dSet_iff.mp hK).1
  have hKK : IsSylow2In K K :=
    ⟨le_rfl, h.thmD.two K hKΩ, fun _ hV' _ hKV' => le_antisymm hV' hKV'⟩
  obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D h.thmD.hyp hW hK hKΩ hKK
  exact (hz.mem_of_le inf_le_left ((h.thmD.two K hKΩ).to_le inf_le_left) (by omega)).2

private theorem ae8ga_twinSet_subset_dSet {Ω : Set (Subgroup G)} (h : EndHyp Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    twinSet Ω R ⊆ DSet Ω W := by
  rintro M ⟨hM, z, hzR, hzM⟩
  exact h.mem_dSet_of_mem hW hM hzM (ae8ga_involution_mem h hW hR hzR)

private theorem ae8ga_cent_iff {y u : G} :
    y ∈ Subgroup.centralizer ({u} : Set G) ↔ y * u = u * y := by
  rw [Subgroup.mem_centralizer_singleton_iff]

private theorem ae8ga_conj_inv_eq (H : Hyp Ω) (F : WFrame Ω W K s g₀) {z : G}
    (hz : IsUniqueInvolution K z) : s * z * s⁻¹ = z := by
  obtain ⟨-, z', hz'K, hz'Ks⟩ := id (H.conjSub_mem_twinSet F.hK F.hs : conjSub s K ∈ twinSet Ω K)
  exact ((hz.conj s).eq hz'Ks).trans (hz.eq hz'K).symm

private theorem ae8ga_isU_conj (H : Hyp Ω) (F : WFrame Ω W K s g₀) {z : G}
    (hz : IsUniqueInvolution K z) : IsUniqueInvolution (conjSub s K) z := by
  have h := hz.conj s
  rwa [ae8ga_conj_inv_eq H F hz] at h

private theorem ae8ga_sq_conj (H : Hyp Ω) (F : WFrame Ω W K s g₀) {z : G}
    (hz : IsUniqueInvolution K z) : (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = z := by
  calc (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = s * (g₀ * g₀) * s⁻¹ := by group
    _ = s * z * s⁻¹ := by rw [Thompson.sq_eq_involution_of_orderOf_four hz F.hg₀.1 F.hg₀4]
    _ = z := ae8ga_conj_inv_eq H F hz

private theorem ae8ga_comm_left {x a b u : G} (hu : u = a * b ∨ u = a * b⁻¹)
    (hxu : x * u = u * x) (hxb : x * b = b * x) : x * a = a * x := by
  have hxb' : Commute x b := hxb
  rcases hu with rfl | rfl
  · have h : x * a * b = a * x * b := by
      calc x * a * b = x * (a * b) := by group
        _ = a * b * x := hxu
        _ = a * (b * x) := by group
        _ = a * (x * b) := by rw [hxb]
        _ = a * x * b := by group
    exact mul_right_cancel h
  · have hxb'' : x * b⁻¹ = b⁻¹ * x := hxb'.inv_right.eq
    have h : x * a * b⁻¹ = a * x * b⁻¹ := by
      calc x * a * b⁻¹ = x * (a * b⁻¹) := by group
        _ = a * b⁻¹ * x := hxu
        _ = a * (b⁻¹ * x) := by group
        _ = a * (x * b⁻¹) := by rw [hxb'']
        _ = a * x * b⁻¹ := by group
    exact mul_right_cancel h

private theorem ae8ga_comm_right {x a b u : G} (hu : u = a * b ∨ u = a * b⁻¹)
    (hxu : x * u = u * x) (hxa : x * a = a * x) : x * b = b * x := by
  have hxa' : Commute x a := hxa
  rcases hu with rfl | rfl
  · have h : a * (x * b) = a * (b * x) := by
      calc a * (x * b) = a * x * b := by group
        _ = x * a * b := by rw [hxa]
        _ = x * (a * b) := by group
        _ = a * b * x := hxu
        _ = a * (b * x) := by group
    exact mul_left_cancel h
  · have h : a * (x * b⁻¹) = a * (b⁻¹ * x) := by
      calc a * (x * b⁻¹) = a * x * b⁻¹ := by group
        _ = x * a * b⁻¹ := by rw [hxa]
        _ = x * (a * b⁻¹) := by group
        _ = a * b⁻¹ * x := hxu
        _ = a * (b⁻¹ * x) := by group
    have hb : Commute x b⁻¹ := mul_left_cancel h
    exact Commute.inv_right_iff.mp hb

private theorem ae8ga_mem_centMembers {J K Ks : Subgroup G} {g₀ g₁ u : G}
    (hJΩ : J ∈ Ω) (hJK : Commutes J K) (hJKs : Commutes J Ks) (hg₀ : g₀ ∈ K) (hg₁ : g₁ ∈ Ks)
    (hu : u = g₀ * g₁ ∨ u = g₀ * g₁⁻¹) : J ∈ Generic.centMembers Ω u := by
  refine ⟨hJΩ, fun x hx => ?_⟩
  have hc0 : Commute x g₀ := hJK x hx g₀ hg₀
  have hc1 : Commute x g₁ := hJKs x hx g₁ hg₁
  rw [ae8ga_cent_iff]
  rcases hu with rfl | rfl
  · exact (hc0.mul_right hc1).eq
  · exact (hc0.mul_right hc1.inv_right).eq

private theorem ae8ga_conj_mem_W (H : Hyp Ω) (F : WFrame Ω W K s g₀) : s * g₀ * s⁻¹ ∈ W :=
  (Subgroup.mem_normalizer_iff.mp (H.pCore_le_normalizer F.hW (H.endHyp.zGroup_le_pCore F.hs))
    g₀).mp F.hg₀.2

private theorem ae8ga_orderOf_conj (s g₀ : G) : orderOf (s * g₀ * s⁻¹) = orderOf g₀ :=
  orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective g₀

private theorem ae8ga_adj_of (H : Hyp Ω) (F : WFrame Ω W K s g₀) {v : G}
    (hv : v ∈ conjSub s K ⊓ W) (hv4 : orderOf v = 4) :
    ∃ R ∈ Generic.centMembers Ω (g₀ * v), ∃ T ∈ Generic.centMembers Ω (g₀ * v),
      T ∈ omegaStarNbr Ω R ∧ T ∉ KPerp Ω R := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution F.hK
  have hP : Q3CL.PartIHypG Ω := ⟨H.endHyp.thmD.hyp, H.endHyp.cls, H.endHyp.thmD.aEmpty⟩
  have hKV : K ∈ twinSet Ω K := ⟨F.hK, z, hz, hz⟩
  have hKD : K ∈ DSet Ω W := F.hV hKV
  have hKsV : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet F.hK F.hs
  have hKsD : conjSub s K ∈ DSet Ω W := F.hV hKsV
  have hcKKs := (H.sup_twin hz hKV hKsV (Ne.symm F.hsK)).1
  obtain ⟨r₁, hr₁, hr₁W⟩ :=
    Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hKD
  obtain ⟨r₂, hr₂, hr₂W⟩ :=
    Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hKsD
  have hN₁ : r₁ ∈ Subgroup.normalizer (W : Set G) := (H.endHyp.mem_dSet_iff.mp hKD).2 hr₁
  have hN₂ : r₂ ∈ Subgroup.normalizer (W : Set G) := (H.endHyp.mem_dSet_iff.mp hKsD).2 hr₂
  have hcomm : Thompson.piG W r₁ * Thompson.piG W r₂ =
      Thompson.piG W r₂ * Thompson.piG W r₁ := by
    rw [← Thompson.piG_mul hN₁ hN₂, ← Thompson.piG_mul hN₂ hN₁, hcKKs r₁ hr₁ r₂ hr₂]
  let ρK : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hKD hr₁ hr₁W
  let ρKs : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hKsD hr₂ hr₂W
  have hne : Thompson.piG W r₁ ≠ Thompson.piG W r₂ := by
    intro e
    have e' : MuTab.muTabElt ρK = MuTab.muTabElt ρKs :=
      Subtype.ext (by rw [MuTab.muTabElt_coe, MuTab.muTabElt_coe]; exact e)
    exact F.hsK ((Q3T6.Mu.muTabElt_eq_iff hP F.hW ρK ρKs).mp e').symm
  have hDC : DComm W K (conjSub s K) :=
    Q3T8.Asc77.Thompson.dComm_of_commute H.endHyp.thmD.hyp F.hW hKD hKsD hr₁ hr₂ hr₁W hr₂W
      hcomm hne
  have hc' : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP F.hW
  have hTT := Q3T6.Mu.isTT_muDelta hP F.hW
  have hS := Q3T6.Mu.isStar_muDelta hc'
  have hnc : ¬ DbarConnected Ω W := H.endHyp.not_dbarConnected F.hW
  obtain ⟨a, haΔ, hconn⟩ := Q3T6.Mu.exists_not_conn_at hP F.hW hnc (MuTab.muTabElt ρK)
  have hKPD : KPerp Ω K ⊆ DSet Ω W := by
    rw [H.kPerp_eq_twinSet F.hK]
    exact F.hV
  have hcls : (KPerp Ω K ∩ DSet Ω W).ncard = 4 := by
    rw [Set.inter_eq_left.mpr hKPD, H.kPerp_eq_twinSet F.hK]
    exact H.ncard_twinSet F.hK
  have hk : (Star3T.cent (Thompson.muDelta Ω W) (MuTab.muTabElt ρK)).ncard = 4 := by
    rw [← ae8ga_ncard_eq H.endHyp F.hW hKD ρK rfl]
    exact hcls
  obtain ⟨ψ, hψ⟩ := Q3T8.Asc77.Thompson.exists_perm_four_of_wv hc' hTT hS hKD hKsD hDC hr₁ hr₁W
    (MuTab.muTabElt_coe ρK) (MuTab.muTabElt_mem ρK) haΔ hconn hk F.hg₀ hv F.hg₀4 hv4
  obtain ⟨x₁, hx₁, x₂, hx₂, hnc12⟩ := ae8ga_exists_noncomm_pair ψ hψ
  obtain ⟨T₁, hT₁C, t₁, ht₁, ht₁W, hx₁e⟩ := hx₁
  obtain ⟨T₂, hT₂C, t₂, ht₂, ht₂W, hx₂e⟩ := hx₂
  let ρ₁ : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hT₁C.1 ht₁ ht₁W
  let ρ₂ : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hT₂C.1 ht₂ ht₂W
  have hm₁ : MuTab.muTabElt ρ₁ = x₁ :=
    Subtype.ext (by rw [MuTab.muTabElt_coe]; exact hx₁e.symm)
  have hm₂ : MuTab.muTabElt ρ₂ = x₂ :=
    Subtype.ext (by rw [MuTab.muTabElt_coe]; exact hx₂e.symm)
  have hnc' : MuTab.muTabElt ρ₁ * MuTab.muTabElt ρ₂ ≠
      MuTab.muTabElt ρ₂ * MuTab.muTabElt ρ₁ := by
    rw [hm₁, hm₂]
    exact hnc12
  have hne12 : ρ₁.K ≠ ρ₂.K := by
    intro e
    apply hnc'
    rw [(Q3T6.Mu.muTabElt_eq_iff hP F.hW ρ₁ ρ₂).mpr e]
  refine ⟨T₁, ⟨(H.endHyp.mem_dSet_iff.mp hT₁C.1).1, hT₁C.2⟩,
    T₂, ⟨(H.endHyp.mem_dSet_iff.mp hT₂C.1).1, hT₂C.2⟩, ?_, ?_⟩
  · exact Q3T6.Mu.muTab_omegaStar hP F.hW ρ₁ ρ₂ hne12
  · intro hm
    rcases Set.mem_insert_iff.mp hm with hm | hm
    · exact hne12 hm.symm
    · exact hnc' ((Q3T6.Mu.muTab_commute_iff hP F.hW ρ₁ ρ₂ hne12).mpr hm)

private theorem ae8ga_omega_symm {Ω : Set (Subgroup G)} (h : EndHyp Ω) (hP : Q3CL.PartIHypG Ω)
    {W X Y : Subgroup G} (hW : W ∈ WSet Ω) (hX : X ∈ DSet Ω W) (hY : Y ∈ DSet Ω W)
    (hne : X ≠ Y) (hn : Y ∈ omegaNbr Ω X) : X ∈ omegaNbr Ω Y := by
  have hc := (Q3T6.Mu.muTab_commute_iff hP hW (ae8ga_rep h hW hX) (ae8ga_rep h hW hY) hne).mpr hn
  exact (Q3T6.Mu.muTab_commute_iff hP hW (ae8ga_rep h hW hY) (ae8ga_rep h hW hX) hne.symm).mp
    hc.symm

private theorem ae8ga_inv_mul_eq {g₀ v z : G} (hz2 : z * z = 1) (hg₀2 : g₀ * g₀ = z)
    (hvv : v * v = z) : g₀⁻¹ * v = g₀ * v * z := by
  have hvz : v * z = v⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, hvv, hz2])
  have hgz' : g₀ * z = g₀⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, hg₀2, hz2])
  have hzv : z * v = v * z := by rw [← hvv, mul_assoc]
  rw [← hgz', mul_assoc, hzv, ← mul_assoc]

theorem mem_zGroup (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹) {z : G}
    (hz : IsUniqueInvolution K z) :
    u ∈ zGroup Ω ∧ u * u = 1 ∧ u ∈ K ⊔ conjSub s K ∧ u ∉ Subgroup.zpowers z := by
  have hΩ : HypOmegaGen Ω := H.endHyp.thmD.hyp
  have hD : (zGroup Ω).Normal := zGroup_normal_of_conjInvariant hΩ.conjInvariant
  have hKV : K ∈ twinSet Ω K := ⟨F.hK, z, hz, hz⟩
  have hKs : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet F.hK F.hs
  obtain ⟨-, z', hz'K, hz'Ks⟩ := id hKs
  have hzz' : z = z' := hz.eq hz'K
  have hsz : s * z * s⁻¹ = z := ((hz.conj s).eq hz'Ks).trans hzz'.symm
  have hzKs : z ∈ conjSub s K := by
    rw [hzz']
    exact hz'Ks.mem
  have hzD : z ∈ zGroup Ω := Subgroup.subset_closure ⟨K, F.hK, hz⟩
  have hsN : s ∈ Subgroup.normalizer (W : Set G) :=
    H.pCore_le_normalizer F.hW (H.endHyp.zGroup_le_pCore F.hs)
  have hg₁W : s * g₀ * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hsN g₀).mp F.hg₀.2
  have hg₀K : g₀ ∈ K := F.hg₀.1
  have hg₀W : g₀ ∈ W := F.hg₀.2
  have hg₁K : s * g₀ * s⁻¹ ∈ conjSub s K := conj_mem_conjSub hg₀K
  have hg₀2 : g₀ * g₀ = z := Thompson.sq_eq_involution_of_orderOf_four hz hg₀K F.hg₀4
  have hg₁2 : (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = z := by
    calc (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = s * (g₀ * g₀) * s⁻¹ := by group
      _ = s * z * s⁻¹ := by rw [hg₀2]
      _ = z := hsz
  have hcomm : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x :=
    Q3CL.Thompson.commutes_of_mem_WSet hΩ F.hW
  have hc10 : (s * g₀ * s⁻¹) * g₀ = g₀ * (s * g₀ * s⁻¹) := hcomm _ hg₁W _ hg₀W
  have hc1 : (s * g₀ * s⁻¹)⁻¹ * g₀ = g₀ * (s * g₀ * s⁻¹)⁻¹ :=
    hcomm _ (W.inv_mem hg₁W) _ hg₀W
  have hd : g₀ * (s * g₀ * s⁻¹)⁻¹ ∈ zGroup Ω := by
    have h1 : g₀ * s * g₀⁻¹ ∈ zGroup Ω := hD.conj_mem s F.hs g₀
    have h2 : g₀ * (s * g₀ * s⁻¹)⁻¹ = (g₀ * s * g₀⁻¹) * s⁻¹ := by group
    rw [h2]
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ F.hs)
  have hgz : g₀ * (s * g₀ * s⁻¹) = g₀ * (s * g₀ * s⁻¹)⁻¹ * z := by
    calc g₀ * (s * g₀ * s⁻¹)
        = g₀ * (s * g₀ * s⁻¹)⁻¹ * ((s * g₀ * s⁻¹) * (s * g₀ * s⁻¹)) := by group
      _ = g₀ * (s * g₀ * s⁻¹)⁻¹ * z := by rw [hg₁2]
  have hsq1 : g₀ * (s * g₀ * s⁻¹) * (g₀ * (s * g₀ * s⁻¹)) = 1 := by
    calc g₀ * (s * g₀ * s⁻¹) * (g₀ * (s * g₀ * s⁻¹))
        = g₀ * ((s * g₀ * s⁻¹) * g₀) * (s * g₀ * s⁻¹) := by group
      _ = g₀ * (g₀ * (s * g₀ * s⁻¹)) * (s * g₀ * s⁻¹) := by rw [hc10]
      _ = (g₀ * g₀) * ((s * g₀ * s⁻¹) * (s * g₀ * s⁻¹)) := by group
      _ = z * z := by rw [hg₀2, hg₁2]
      _ = 1 := hz.sq
  have hinv2 : (s * g₀ * s⁻¹)⁻¹ * (s * g₀ * s⁻¹)⁻¹ = z := by
    rw [← mul_inv_rev, hg₁2, inv_eq_of_mul_eq_one_right hz.sq]
  have hsq2 : g₀ * (s * g₀ * s⁻¹)⁻¹ * (g₀ * (s * g₀ * s⁻¹)⁻¹) = 1 := by
    calc g₀ * (s * g₀ * s⁻¹)⁻¹ * (g₀ * (s * g₀ * s⁻¹)⁻¹)
        = g₀ * ((s * g₀ * s⁻¹)⁻¹ * g₀) * (s * g₀ * s⁻¹)⁻¹ := by group
      _ = g₀ * (g₀ * (s * g₀ * s⁻¹)⁻¹) * (s * g₀ * s⁻¹)⁻¹ := by rw [hc1]
      _ = (g₀ * g₀) * ((s * g₀ * s⁻¹)⁻¹ * (s * g₀ * s⁻¹)⁻¹) := by group
      _ = z * z := by rw [hg₀2, hinv2]
      _ = 1 := hz.sq
  have hKKs : K ⊓ conjSub s K = Subgroup.zpowers z :=
    (H.sup_twin hz hKV hKs (Ne.symm F.hsK)).2.1
  have hzpow : Subgroup.zpowers z ≤ conjSub s K := Subgroup.zpowers_le.mpr hzKs
  have hg₀notin : ¬ (g₀ ∈ K ⊓ conjSub s K) := by
    intro hm
    rw [hKKs] at hm
    have h2 := ae8ga_sq_eq_one_of_mem_zpowers hz.sq hz.ne_one hm
    rw [hg₀2] at h2
    exact hz.ne_one h2
  rcases hu with rfl | rfl
  · refine ⟨?_, hsq1, ?_, ?_⟩
    · rw [hgz]
      exact Subgroup.mul_mem _ hd hzD
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₀K) (Subgroup.mem_sup_right hg₁K)
    · intro hmem
      have hmKs : g₀ * (s * g₀ * s⁻¹) ∈ conjSub s K := hzpow hmem
      have hg₀Ks : g₀ ∈ conjSub s K := by
        have := Subgroup.mul_mem _ hmKs (Subgroup.inv_mem _ hg₁K)
        rwa [mul_inv_cancel_right] at this
      exact hg₀notin ⟨hg₀K, hg₀Ks⟩
  · refine ⟨hd, hsq2, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hg₀K)
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hg₁K))
    · intro hmem
      have hmKs : g₀ * (s * g₀ * s⁻¹)⁻¹ ∈ conjSub s K := hzpow hmem
      have hg₀Ks : g₀ ∈ conjSub s K := by
        have := Subgroup.mul_mem _ hmKs hg₁K
        rwa [inv_mul_cancel_right] at this
      exact hg₀notin ⟨hg₀K, hg₀Ks⟩

theorem twin (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹) :
    ∃ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard = 2 := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution F.hK
  obtain ⟨K₃, hK₃V, h1, h2, h3, h4, h5, hVeq⟩ := H.exists_twin_frame F.hK F.hs F.hsK
  have hKV : K ∈ twinSet Ω K := ⟨F.hK, z, hz, hz⟩
  have hKsV : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet F.hK F.hs
  have hK₄V : conjSub s K₃ ∈ twinSet Ω K := by
    rw [hVeq]
    simp
  have hg₁K : s * g₀ * s⁻¹ ∈ conjSub s K := conj_mem_conjSub F.hg₀.1
  have hg₂ : (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = z := ae8ga_sq_conj H F hz
  have hKsz : IsUniqueInvolution (conjSub s K) z := ae8ga_isU_conj H F hz
  have c₃K := (H.sup_twin hz hK₃V hKV h1).1
  have c₃Ks := (H.sup_twin hz hK₃V hKsV h2).1
  have c₄K := (H.sup_twin hz hK₄V hKV h4).1
  have c₄Ks := (H.sup_twin hz hK₄V hKsV h5).1
  have cKKs := (H.sup_twin hz hKV hKsV (Ne.symm F.hsK)).1
  have hK3P : K₃ ∈ Generic.centMembers Ω u :=
    ae8ga_mem_centMembers hK₃V.1 c₃K c₃Ks F.hg₀.1 hg₁K hu
  have hK4P : conjSub s K₃ ∈ Generic.centMembers Ω u :=
    ae8ga_mem_centMembers hK₄V.1 c₄K c₄Ks F.hg₀.1 hg₁K hu
  have hKnot : K ∉ Generic.centMembers Ω u := by
    rintro ⟨-, hKc⟩
    have hc : ∀ y ∈ K, g₀ * y = y * g₀ := by
      intro y hy
      have hyu : y * u = u * y := ae8ga_cent_iff.mp (hKc hy)
      have hyb : y * (s * g₀ * s⁻¹) = (s * g₀ * s⁻¹) * y := cKKs y hy _ hg₁K
      exact (ae8ga_comm_left hu hyu hyb).symm
    have hg₀z : g₀ ∈ Subgroup.zpowers z :=
      ae8ga_mem_zpowers_of_central H.endHyp F.hK hz F.hg₀.1 hc
    have h2' := ae8ga_sq_eq_one_of_mem_zpowers hz.sq hz.ne_one hg₀z
    rw [Thompson.sq_eq_involution_of_orderOf_four hz F.hg₀.1 F.hg₀4] at h2'
    exact hz.ne_one h2'
  have hKsnot : conjSub s K ∉ Generic.centMembers Ω u := by
    rintro ⟨-, hKc⟩
    have hc : ∀ y ∈ conjSub s K, (s * g₀ * s⁻¹) * y = y * (s * g₀ * s⁻¹) := by
      intro y hy
      have hyu : y * u = u * y := ae8ga_cent_iff.mp (hKc hy)
      have hyg : y * g₀ = g₀ * y := (cKKs g₀ F.hg₀.1 y hy).symm
      exact (ae8ga_comm_right hu hyu hyg).symm
    have hg₁z : (s * g₀ * s⁻¹) ∈ Subgroup.zpowers z :=
      ae8ga_mem_zpowers_of_central H.endHyp hKsV.1 hKsz hg₁K hc
    have h2' := ae8ga_sq_eq_one_of_mem_zpowers hz.sq hz.ne_one hg₁z
    rw [hg₂] at h2'
    exact hz.ne_one h2'
  refine ⟨K₃, hK3P, ?_⟩
  have hsetE : twinSet Ω K₃ ∩ Generic.centMembers Ω u = {K₃, conjSub s K₃} := by
    rw [ae8ga_twinSet_eq hK₃V, hVeq]
    ext x
    constructor
    · rintro ⟨hx, hxP⟩
      rcases hx with hx | hx | hx | hx
      · exact absurd (hx ▸ hxP) hKnot
      · exact absurd (hx ▸ hxP) hKsnot
      · exact Or.inl hx
      · exact Or.inr hx
    · rintro (rfl | rfl)
      · exact ⟨by simp, hK3P⟩
      · exact ⟨by simp, hK4P⟩
  rw [hsetE]
  exact Set.ncard_pair h3.symm

theorem adj (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹) :
    ∃ R ∈ Generic.centMembers Ω u, ∃ T ∈ Generic.centMembers Ω u,
      T ∈ omegaStarNbr Ω R ∧ T ∉ KPerp Ω R := by
  have hg₁W : s * g₀ * s⁻¹ ∈ W := ae8ga_conj_mem_W H F
  have hg₁K : s * g₀ * s⁻¹ ∈ conjSub s K := conj_mem_conjSub F.hg₀.1
  have hg₁o : orderOf (s * g₀ * s⁻¹) = 4 := by
    rw [ae8ga_orderOf_conj]
    exact F.hg₀4
  rcases hu with rfl | rfl
  · exact ae8ga_adj_of H F ⟨hg₁K, hg₁W⟩ hg₁o
  · exact ae8ga_adj_of H F (v := (s * g₀ * s⁻¹)⁻¹)
      ⟨Subgroup.inv_mem _ hg₁K, W.inv_mem hg₁W⟩ (by rw [orderOf_inv]; exact hg₁o)

theorem exists_twin_le_centralizer (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹)
    (hP2 : ∀ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard ≤ 2)
    {L : Subgroup G} (hL : L ∈ DSet Ω W) :
    ∃ R ∈ twinSet Ω L, R ∈ DSet Ω W ∧ R ≤ Subgroup.centralizer ({u} : Set G) := by
  have hLΩ : L ∈ Ω := (H.endHyp.mem_dSet_iff.mp hL).1
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution F.hK
  have hKV : K ∈ twinSet Ω K := ⟨F.hK, z, hz, hz⟩
  have hKsV : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet F.hK F.hs
  have hKD : K ∈ DSet Ω W := F.hV hKV
  have hKsD : conjSub s K ∈ DSet Ω W := F.hV hKsV
  have hP : Q3CL.PartIHypG Ω := ⟨H.endHyp.thmD.hyp, H.endHyp.cls, H.endHyp.thmD.aEmpty⟩
  obtain ⟨K₃, hK₃V, h1, h2, h3, h4, h5, hVeq⟩ := H.exists_twin_frame F.hK F.hs F.hsK
  have hg₁K : s * g₀ * s⁻¹ ∈ conjSub s K := conj_mem_conjSub F.hg₀.1
  have hg₁W : s * g₀ * s⁻¹ ∈ W := ae8ga_conj_mem_W H F
  have hg₂ : (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = z := ae8ga_sq_conj H F hz
  have hKsz : IsUniqueInvolution (conjSub s K) z := ae8ga_isU_conj H F hz
  have hg₀2 : g₀ * g₀ = z := Thompson.sq_eq_involution_of_orderOf_four hz F.hg₀.1 F.hg₀4
  have cKKs := (H.sup_twin hz hKV hKsV (Ne.symm F.hsK)).1
  have hKs_om : conjSub s K ∈ omegaNbr Ω K :=
    (TC.mem_omegaNbr_iff H.endHyp.thmD.hyp H.endHyp.thmD.two).mpr
      ⟨hKsV.1, F.hsK, Asc77.AscL62.le_normalizer_of_commutes cKKs.symm⟩
  by_cases hLK : L ∈ twinSet Ω K
  · refine ⟨K₃, ?_, F.hV hK₃V, ?_⟩
    · rw [ae8ga_twinSet_eq hLK]
      exact hK₃V
    · have c₃K := (H.sup_twin hz hK₃V hKV h1).1
      have c₃Ks := (H.sup_twin hz hK₃V hKsV h2).1
      exact (ae8ga_mem_centMembers hK₃V.1 c₃K c₃Ks F.hg₀.1 hg₁K hu).2
  · by_contra hcon
    have hsub : twinSet Ω L ⊆ DSet Ω W := ae8ga_twinSet_subset_dSet H.endHyp F.hW hL
    have hnot : ∀ M ∈ twinSet Ω L, ¬ M ≤ Subgroup.centralizer ({u} : Set G) :=
      fun M hM hle => hcon ⟨M, hM, hsub hM, hle⟩
    obtain ⟨zL, hzL⟩ := H.endHyp.exists_isUniqueInvolution hLΩ
    have hLself : L ∈ twinSet Ω L := ⟨hLΩ, zL, hzL, hzL⟩
    have hMK : ∀ M ∈ twinSet Ω L, M ∉ twinSet Ω K := by
      intro M hM hMK'
      have e1 := ae8ga_twinSet_eq hM
      have e2 := ae8ga_twinSet_eq hMK'
      apply hLK
      have hLM : L ∈ twinSet Ω M := by
        rw [e1]
        exact hLself
      rw [e2] at hLM
      exact hLM
    obtain ⟨v, hv, hvv, huv⟩ : ∃ v : G, v ∈ conjSub s K ⊓ W ∧ v * v = z ∧ u = g₀ * v := by
      rcases hu with h | h
      · exact ⟨s * g₀ * s⁻¹, ⟨hg₁K, hg₁W⟩, hg₂, h⟩
      · refine ⟨(s * g₀ * s⁻¹)⁻¹, ⟨Subgroup.inv_mem _ hg₁K, W.inv_mem hg₁W⟩, ?_, h⟩
        rw [← mul_inv_rev, hg₂, inv_eq_of_mul_eq_one_right hz.sq]
    have hUW : u ∈ W := by
      rw [huv]
      exact W.mul_mem F.hg₀.2 hv.2
    have hzW : z ∈ W := by
      rw [← hg₀2]
      exact W.mul_mem F.hg₀.2 F.hg₀.2
    have hgv : g₀⁻¹ * v = u * z := by
      rw [ae8ga_inv_mul_eq hz.sq hg₀2 hvv, huv]
    obtain ⟨r₁, hr₁, hr₁W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hKD
    obtain ⟨r₂, hr₂, hr₂W⟩ :=
      Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hKsD
    let ρK : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hKD hr₁ hr₁W
    let ρKs : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hKsD hr₂ hr₂W
    let c : Q3CL.Thompson.Ctx Ω W := Q3CL.T8.ctxOf hP F.hW
    have hconjK : r₁ * g₀ * r₁⁻¹ = g₀⁻¹ := c.conj_inv ρK F.hg₀
    have hcentr : r₁ * v = v * r₁ := c.centralizes ρK ρKs hKs_om hv
    have hcv : r₁ * v * r₁⁻¹ = v := by rw [hcentr, mul_assoc, mul_inv_cancel, mul_one]
    have hr1z : r₁ * z * r₁⁻¹ = z := by
      calc r₁ * z * r₁⁻¹ = r₁ * (g₀ * g₀) * r₁⁻¹ := by rw [hg₀2]
        _ = (r₁ * g₀ * r₁⁻¹) * (r₁ * g₀ * r₁⁻¹) := by group
        _ = g₀⁻¹ * g₀⁻¹ := by rw [hconjK]
        _ = (g₀ * g₀)⁻¹ := by rw [mul_inv_rev]
        _ = z := by
          rw [hg₀2]
          exact inv_eq_of_mul_eq_one_right hz.sq
    have hconj_uz : r₁ * (u * z) * r₁⁻¹ = u := by
      calc r₁ * (u * z) * r₁⁻¹ = r₁ * (g₀ * v * z) * r₁⁻¹ := by rw [huv]
        _ = (r₁ * g₀ * r₁⁻¹) * (r₁ * v * r₁⁻¹) * (r₁ * z * r₁⁻¹) := by group
        _ = g₀⁻¹ * v * z := by rw [hconjK, hcv, hr1z]
        _ = g₀ * v * z * z := by rw [ae8ga_inv_mul_eq hz.sq hg₀2 hvv]
        _ = u := by rw [huv, mul_assoc, hz.sq, mul_one]
    have hcent : ∀ M ∈ twinSet Ω L, M ≤ Subgroup.centralizer ({u * z} : Set G) := by
      intro M hM
      obtain ⟨hMΩ, zM, hzLM, hzM⟩ := id hM
      have hMD : M ∈ DSet Ω W := hsub hM
      have hMK_ne : M ≠ K := fun e => hMK M hM (e ▸ hKV)
      have hMKs_ne : M ≠ conjSub s K := fun e => hMK M hM (e ▸ hKsV)
      have hnotK1 : K ∉ omegaNbr Ω M := fun hKM => hMK M hM (by
        have hMK2 := ae8ga_omega_symm H.endHyp hP F.hW hMD hKD hMK_ne hKM
        rw [← H.kPerp_eq_twinSet F.hK]
        exact Set.mem_insert_of_mem _ hMK2)
      have hnotK2 : conjSub s K ∉ omegaNbr Ω M := fun hKsM => hMK M hM (by
        have hMK2 := ae8ga_omega_symm H.endHyp hP F.hW hMD hKsD hMKs_ne hKsM
        have hKP : M ∈ KPerp Ω (conjSub s K) := Set.mem_insert_of_mem _ hMK2
        rw [H.kPerp_eq_twinSet hKsV.1, ae8ga_twinSet_eq hKsV] at hKP
        exact hKP)
      obtain ⟨rM, hrM, hrMW⟩ :=
        Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hMD
      let ρM : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hMD hrM hrMW
      have hd := c.stab_dichotomy ρM ρK ρKs hMK_ne hMKs_ne hnotK1 hnotK2 F.hg₀ hv hzM hz hKsz
        hg₀2 hvv
      rw [hgv] at hd
      rcases hd with hd | hd
      · exfalso
        have huc : rM * u = u * rM := by
          rw [huv]
          exact (mul_inv_eq_iff_eq_mul).mp hd
        exact hnot M hM (Q3CL.Thompson.le_centralizer_of_mem H.endHyp.thmD.hyp F.hW hMD hrM hrMW
          hUW huc)
      · have huz : u * z ∈ W := W.mul_mem hUW hzW
        exact Q3CL.Thompson.le_centralizer_of_mem H.endHyp.thmD.hyp F.hW hMD hrM hrMW huz
          ((mul_inv_eq_iff_eq_mul).mp hd)
    have hconjC : ∀ M ∈ twinSet Ω L, conjSub r₁ M ≤ Subgroup.centralizer ({u} : Set G) := by
      intro M hM x hx
      have hm := mem_conjSub_iff.mp hx
      have hmc : (r₁⁻¹ * x * r₁) * (u * z) = (u * z) * (r₁⁻¹ * x * r₁) :=
        ae8ga_cent_iff.mp (hcent M hM hm)
      rw [ae8ga_cent_iff]
      calc x * u = (r₁ * (r₁⁻¹ * x * r₁) * r₁⁻¹) * (r₁ * (u * z) * r₁⁻¹) := by
            rw [hconj_uz]; group
        _ = r₁ * ((r₁⁻¹ * x * r₁) * (u * z)) * r₁⁻¹ := by group
        _ = r₁ * ((u * z) * (r₁⁻¹ * x * r₁)) * r₁⁻¹ := by rw [hmc]
        _ = (r₁ * (u * z) * r₁⁻¹) * (r₁ * (r₁⁻¹ * x * r₁) * r₁⁻¹) := by group
        _ = u * x := by rw [hconj_uz]; group
    have hM₀C : conjSub r₁ L ∈ Generic.centMembers Ω u :=
      ⟨H.endHyp.thmD.hyp.conjInvariant r₁ L hLΩ, hconjC L hLself⟩
    have hsetsub : (conjSub r₁) '' (twinSet Ω L) ⊆
        twinSet Ω (conjSub r₁ L) ∩ Generic.centMembers Ω u := by
      rintro _ ⟨M, hM, rfl⟩
      obtain ⟨hMΩ, zM, hzLM, hzM⟩ := id hM
      have hzMz : IsUniqueInvolution M zL := by
        rw [hzL.eq hzLM]
        exact hzM
      refine ⟨⟨H.endHyp.thmD.hyp.conjInvariant r₁ M hMΩ, r₁ * zL * r₁⁻¹,
        hzL.conj r₁, hzMz.conj r₁⟩, ⟨H.endHyp.thmD.hyp.conjInvariant r₁ M hMΩ,
          hconjC M hM⟩⟩
    have hcard : ((conjSub r₁) '' (twinSet Ω L)).ncard = 4 := by
      rw [Set.ncard_image_of_injective _ (conjSub_injective r₁)]
      exact H.ncard_twinSet hLΩ
    have hle4 := Set.ncard_le_ncard hsetsub
    have h2' := hP2 (conjSub r₁ L) hM₀C
    omega

private theorem ae8gb_mem_of_USet {Ω : Set (Subgroup G)} (h : EndHyp Ω) {L : Subgroup G}
    (hL : L ∈ Ω) {z : G} (hz : IsUniqueInvolution L z) {U : Subgroup G} (hU : U ∈ USet Ω)
    (hUL : U ≤ L) : z ∈ U := by
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet h.thmD.hyp hU
  have hdvd : Nat.card U ∣ 8 := by
    rw [← h.card_eq_eight hL]
    exact Subgroup.card_dvd_of_le hUL
  have h2 : 2 ∣ Nat.card U := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card U = m := ⟨_, rfl⟩
    rw [hm] at hdvd h4 ⊢
    have hle : m ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases m <;> omega
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 h2
  have hy2 : y ^ 2 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have hy1 : y ≠ 1 := by
    intro e
    rw [e, orderOf_one] at hy
    norm_num at hy
  have hyG : ((y : U) : G) * ((y : U) : G) = 1 := by
    have h' := congrArg Subtype.val hy2
    rw [pow_two] at h'
    simpa only [Subgroup.coe_mul, Subgroup.coe_one] using h'
  have hyL : ((y : U) : G) ∈ L := hUL y.2
  have hyne : ((y : U) : G) ≠ 1 := fun e => hy1 (Subtype.ext e)
  rcases hz.unique _ hyL hyG with e | e
  · exact absurd e hyne
  · rw [← e]
    exact y.2

theorem exists_twin_cent (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹)
    (hP2 : ∀ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard ≤ 2)
    {L : Subgroup G} (hL : L ∈ Ω) (huL : u ∈ Subgroup.normalizer (L : Set G)) :
    ∃ R ∈ Generic.centMembers Ω u, R ∈ twinSet Ω L := by
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp F.hK
  have hudz : u ∈ zGroup Ω := (mem_zGroup H F hu hzK).1
  obtain ⟨x, hxL, hx4, hxu⟩ := H.exists_order_four_centralizes hL hudz huL
  have hg0W : g₀ ∈ W := (Subgroup.mem_inf.mp F.hg₀).2
  have hs_eq : conjSub s W = W :=
    mem_normalizer_iff_conjSub_eq.mp (H.pCore_le_normalizer F.hW (H.endHyp.zGroup_le_pCore F.hs))
  have hsW : ∀ w ∈ W, s * w * s⁻¹ ∈ W := fun w hw => by
    have := conj_mem_conjSub (n := s) hw
    rwa [hs_eq] at this
  have huW : u ∈ W := by
    rcases hu with rfl | rfl
    · exact W.mul_mem hg0W (hsW g₀ hg0W)
    · exact W.mul_mem hg0W (W.inv_mem (hsW g₀ hg0W))
  have hWabel : ∀ w ∈ W, ∀ v ∈ W, w * v = v * w := by
    obtain ⟨η, hη, hWeq⟩ := F.hW
    rw [hWeq]
    exact fun w hw v hv => TC.etaSpan_comm H.endHyp.thmD.hyp hη w hw v hv
  have hWle : W ≤ Subgroup.centralizer ({u} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hWabel w hw u huW)
  have hXC : Subgroup.zpowers x ≤ Subgroup.centralizer ({u} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxu)
  have hX2 : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hx4]; norm_num)
  obtain ⟨V, hV, hXV⟩ := IsSylow2In.exists_ge hX2 hXC
  have hW2 : IsPGroup 2 W := by
    obtain ⟨η, hη, hWeq⟩ := F.hW
    obtain ⟨S₀, hηS₀, -⟩ := hη
    rw [hWeq]
    exact S₀.isPGroup'.to_le (iSup₂_le fun U hU => (hηS₀.1 hU).2)
  obtain ⟨y, hyC, hWy⟩ := Sec7.exists_conj_le_of_isSylow2In hV hW2 hWle
  obtain ⟨c, hcu, hcW⟩ : ∃ c : G, Commute c u ∧ conjSub c W ≤ V :=
    ⟨y⁻¹, Commute.inv_left_iff.mpr (Subgroup.mem_centralizer_singleton_iff.mp hyC),
      by
        calc conjSub y⁻¹ W ≤ conjSub y⁻¹ (conjSub y V) := conjSub_mono hWy
          _ = V := conjSub_inv_conjSub y V⟩
  obtain ⟨S, hVS⟩ := hV.2.1.exists_le_sylow
  have hWc : conjSub c W ∈ WSet Ω := WSet.conj H.endHyp.thmD.hyp.conjInvariant F.hW c
  obtain ⟨η', hη', hWc_eq⟩ := hWc
  obtain ⟨S₁, hηS₁, -⟩ := id hη'
  have hηle : ∀ V' ∈ η', V' ≤ (S : Subgroup G) := fun V' hV' => by
    have h1 : V' ≤ conjSub c W := by
      rw [hWc_eq]
      exact le_iSup₂ (f := fun (U : Subgroup G) (_ : U ∈ η') => U) V' hV'
    exact h1.trans (hcW.trans hVS)
  have hxS : x ∈ (S : Subgroup G) := hVS (hXV (Subgroup.mem_zpowers x))
  have h2 : 2 < Nat.card ↥(L ⊓ (S : Subgroup G)) := by
    have hX : Subgroup.zpowers x ≤ L ⊓ (S : Subgroup G) :=
      le_inf (Subgroup.zpowers_le.mpr hxL) (Subgroup.zpowers_le.mpr hxS)
    have hc := Subgroup.card_le_of_le hX
    rw [Nat.card_zpowers, hx4] at hc
    omega
  have hLη : L ⊓ (⨆ U ∈ η', U) ∈ η' :=
    Sec6Gen.l6_11Gen G Ω H.endHyp.thmD.hyp S η' hη' hηle L hL h2
  have hUS : L ⊓ (⨆ U ∈ η', U) ∈ USet Ω := (hηS₁.1 hLη).1
  obtain ⟨zL, hzL⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp hL
  have hzW : zL ∈ conjSub c W := by
    rw [hWc_eq]
    exact (Subgroup.mem_inf.mp (ae8gb_mem_of_USet H.endHyp hL hzL hUS inf_le_left)).2
  have hzL0 : IsUniqueInvolution (conjSub c⁻¹ L) (c⁻¹ * zL * c) := by
    have := hzL.conj c⁻¹
    rwa [inv_inv] at this
  have hzW0 : c⁻¹ * zL * c ∈ W := mem_conjSub_iff.mp hzW
  have hL0 : conjSub c⁻¹ L ∈ Ω := H.endHyp.thmD.hyp.conjInvariant c⁻¹ L hL
  have hL0D : conjSub c⁻¹ L ∈ DSet Ω W := H.endHyp.mem_dSet_of_mem F.hW hL0 hzL0 hzW0
  obtain ⟨R₀, hR₀tw, -, hR₀C⟩ := exists_twin_le_centralizer H F hu hP2 hL0D
  have hR₀P : R₀ ∈ Generic.centMembers Ω u := ⟨hR₀tw.1, hR₀C⟩
  refine ⟨conjSub c R₀, AE8End.SectData.ae8a_conjSub_mem H hcu hR₀P, ?_⟩
  have htw := AE8End.SectData.ae8a_twin_conj H c hR₀tw
  rwa [conjSub_conjSub_inv] at htw

section FrameCert


theorem mem_pSpan (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹)
    (hP2 : ∀ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard ≤ 2) :
    u ∈ pSpan (Generic.centMembers Ω u) := by
  obtain ⟨z, hz⟩ := H.endHyp.exists_isUniqueInvolution F.hK
  obtain ⟨K₃, hK₃V, h1, h2, h3, h4, h5, hVeq⟩ := H.exists_twin_frame F.hK F.hs F.hsK
  have hP : Q3CL.PartIHypG Ω := ⟨H.endHyp.thmD.hyp, H.endHyp.cls, H.endHyp.thmD.aEmpty⟩
  have hKV : K ∈ twinSet Ω K := ⟨F.hK, z, hz, hz⟩
  have hKsV : conjSub s K ∈ twinSet Ω K := H.conjSub_mem_twinSet F.hK F.hs
  have hK₃Ω : K₃ ∈ Ω := hK₃V.1
  have hK₃z : IsUniqueInvolution K₃ z := by
    obtain ⟨-, z', hz'K, hz'K₃⟩ := id hK₃V
    rw [hz.eq hz'K]
    exact hz'K₃
  have hKsz : IsUniqueInvolution (conjSub s K) z := ae8ga_isU_conj H F hz
  have hg₁K : s * g₀ * s⁻¹ ∈ conjSub s K := conj_mem_conjSub F.hg₀.1
  have hg₁W : s * g₀ * s⁻¹ ∈ W := ae8ga_conj_mem_W H F
  have hg₂ : (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = z := ae8ga_sq_conj H F hz
  have hg₀2 : g₀ * g₀ = z := Thompson.sq_eq_involution_of_orderOf_four hz F.hg₀.1 F.hg₀4
  have c₃K := (H.sup_twin hz hK₃V hKV h1).1
  have c₃Ks := (H.sup_twin hz hK₃V hKsV h2).1
  have cKKs := (H.sup_twin hz hKV hKsV (Ne.symm F.hsK)).1
  have hK3P : K₃ ∈ Generic.centMembers Ω u :=
    ae8ga_mem_centMembers hK₃Ω c₃K c₃Ks F.hg₀.1 hg₁K hu
  have hKD : K ∈ DSet Ω W := F.hV hKV
  have hKsD : conjSub s K ∈ DSet Ω W := F.hV hKsV
  have hK₃D : K₃ ∈ DSet Ω W := F.hV hK₃V
  obtain ⟨r₁, hr₁, hr₁W⟩ := Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hKD
  obtain ⟨r₂, hr₂, hr₂W⟩ :=
    Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hKsD
  obtain ⟨r₃, hr₃, hr₃W⟩ :=
    Q3CL.Thompson.exists_not_mem_of_mem_D H.endHyp.thmD.hyp F.hW hK₃D
  let ρa : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hKD hr₁ hr₁W
  let ρb : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hKsD hr₂ hr₂W
  let ρc : Asc77.Thompson.Rep Ω W := ae8ga_repOf H.endHyp hK₃D hr₃ hr₃W
  have hab : MuTab.muTabElt ρa ≠ MuTab.muTabElt ρb := fun e =>
    F.hsK ((Q3T6.Mu.muTabElt_eq_iff hP F.hW ρa ρb).mp e).symm
  have hac : MuTab.muTabElt ρa ≠ MuTab.muTabElt ρc := fun e =>
    h1 ((Q3T6.Mu.muTabElt_eq_iff hP F.hW ρa ρc).mp e).symm
  have hbc : MuTab.muTabElt ρb ≠ MuTab.muTabElt ρc := fun e =>
    h2 ((Q3T6.Mu.muTabElt_eq_iff hP F.hW ρb ρc).mp e).symm
  have hKsN : conjSub s K ≤ Subgroup.normalizer (K : Set G) :=
    Asc77.AscL62.le_normalizer_of_commutes cKKs.symm
  have hKs_om : conjSub s K ∈ omegaNbr Ω K :=
    (TC.mem_omegaNbr_iff H.endHyp.thmD.hyp H.endHyp.thmD.two).mpr ⟨hKsV.1, F.hsK, hKsN⟩
  have hK3_om : K₃ ∈ omegaNbr Ω K :=
    (TC.mem_omegaNbr_iff H.endHyp.thmD.hyp H.endHyp.thmD.two).mpr
      ⟨hK₃Ω, h1, Asc77.AscL62.le_normalizer_of_commutes c₃K⟩
  have hK3_omKs : K₃ ∈ omegaNbr Ω (conjSub s K) :=
    (TC.mem_omegaNbr_iff H.endHyp.thmD.hyp H.endHyp.thmD.two).mpr
      ⟨hK₃Ω, h2, Asc77.AscL62.le_normalizer_of_commutes c₃Ks⟩
  have cab : MuTab.muTabElt ρa * MuTab.muTabElt ρb = MuTab.muTabElt ρb * MuTab.muTabElt ρa :=
    (Q3T6.Mu.muTab_commute_iff hP F.hW ρa ρb (Ne.symm F.hsK)).mpr hKs_om
  have cac : MuTab.muTabElt ρa * MuTab.muTabElt ρc = MuTab.muTabElt ρc * MuTab.muTabElt ρa :=
    (Q3T6.Mu.muTab_commute_iff hP F.hW ρa ρc (Ne.symm h1)).mpr hK3_om
  have cbc : MuTab.muTabElt ρb * MuTab.muTabElt ρc = MuTab.muTabElt ρc * MuTab.muTabElt ρb :=
    (Q3T6.Mu.muTab_commute_iff hP F.hW ρb ρc (Ne.symm h2)).mpr hK3_omKs
  have hnc : ¬ DbarConnected Ω W := H.endHyp.not_dbarConnected F.hW
  have hcd : PhilipHall.Frame.TwinMu.cdSub Ω W u ≤ pSpan (Generic.centMembers Ω u) := by
    unfold PhilipHall.Frame.TwinMu.cdSub
    refine iSup₂_le fun T hT => ?_
    exact le_pSpan ⟨(H.endHyp.mem_dSet_iff.mp hT.1).1, hT.2⟩
  have hzP : z ∈ pSpan (Generic.centMembers Ω u) := le_pSpan hK3P hK₃z.mem
  have hstep : ∀ v : G, v ∈ conjSub s K ⊓ W → orderOf v = 4 → v * v = z → u = g₀ * v →
      u * z ∈ pSpan (Generic.centMembers Ω u) := by
    intro v hv hv4 hvv huv
    obtain ⟨ρS, hSle, hconnS⟩ :=
      PhilipHall.Frame.TwinMu.exists_S hP F.hW hnc hab hac hbc cab cac F.hg₀ hv F.hg₀4 hv4
    have hlay := PhilipHall.Frame.TwinMu.layer_mem hP F.hW hab hac hbc cab cac cbc hconnS
      F.hg₀ hv hz hKsz hK₃z hg₀2 hvv hSle
    have hvz : v * z = v⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, hvv, hz.sq])
    have hgz' : g₀ * z = g₀⁻¹ := eq_inv_of_mul_eq_one_right (by rw [← mul_assoc, hg₀2, hz.sq])
    have hzv : z * v = v * z := by rw [← hvv, mul_assoc]
    have hid1 : g₀ * v⁻¹ = g₀ * v * z := by rw [← hvz, mul_assoc]
    have hid2 : g₀⁻¹ * v = g₀ * v * z := by
      rw [← hgz', mul_assoc, hzv, ← mul_assoc]
    have hmem : (g₀ * v) * z ∈ PhilipHall.Frame.TwinMu.cdSub Ω W (g₀ * v) := by
      rcases hlay with h | h
      · rwa [hid1] at h
      · rwa [hid2] at h
    rw [← huv] at hmem
    exact hcd hmem
  rcases hu with hu1 | hu2
  · have := hstep (s * g₀ * s⁻¹) ⟨hg₁K, hg₁W⟩ (by rw [ae8ga_orderOf_conj]; exact F.hg₀4) hg₂ hu1
    have h' := Subgroup.mul_mem _ this hzP
    rwa [mul_assoc, hz.sq, mul_one] at h'
  · have hinv2 : (s * g₀ * s⁻¹)⁻¹ * (s * g₀ * s⁻¹)⁻¹ = z := by
      rw [← mul_inv_rev, hg₂, inv_eq_of_mul_eq_one_right hz.sq]
    have := hstep (s * g₀ * s⁻¹)⁻¹ ⟨Subgroup.inv_mem _ hg₁K, W.inv_mem hg₁W⟩
      (by rw [orderOf_inv, ae8ga_orderOf_conj]; exact F.hg₀4) hinv2 hu2
    have h' := Subgroup.mul_mem _ this hzP
    rwa [mul_assoc, hz.sq, mul_one] at h'

end FrameCert

theorem bad (H : Hyp Ω) (F : WFrame Ω W K s g₀) {u : G}
    (hu : u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹)
    (hP2 : ∀ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard ≤ 2)
    {J : Subgroup G} (hJ : J ∈ Ω) (hJs : IsUniqueInvolution J s)
    (huJ : u ∈ Subgroup.normalizer (J : Set G)) :
    ∃ L ∈ Generic.centMembers Ω u, ∃ J' ∈ Generic.centMembers Ω u,
      J' ∉ KPerp Ω L ∧ J' ∉ omegaStarNbr Ω L := by
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp F.hK
  have hKD : K ∈ DSet Ω W := F.hV ⟨F.hK, zK, hzK, hzK⟩
  obtain ⟨L, hLtw, -, hLC⟩ := exists_twin_le_centralizer H F hu hP2 hKD
  have hLP : L ∈ Generic.centMembers Ω u := ⟨hLtw.1, hLC⟩
  have hsN : s ∉ Subgroup.normalizer (L : Set G) := by
    intro h
    have h1 : s ∈ zGroup Ω ⊓ Subgroup.normalizer (L : Set G) :=
      Subgroup.mem_inf.mpr ⟨F.hs, h⟩
    rw [← H.zGroup_inf_normalizer_eq F.hK hLtw] at h1
    exact F.hsK (mem_normalizer_iff_conjSub_eq.mp (Subgroup.mem_inf.mp h1).2)
  obtain ⟨J', hJ'P, hJ'tw⟩ := exists_twin_cent H F hu hP2 hJ huJ
  have hJ's : IsUniqueInvolution J' s := by
    obtain ⟨-, z, hJz, hJ'z⟩ := hJ'tw
    have hzs : z = s := hJz.eq hJs
    rw [hzs] at hJ'z
    exact hJ'z
  refine ⟨L, hLP, J', hJ'P, ?_, ?_⟩
  · rw [H.kPerp_eq_twinSet hLtw.1]
    intro hc
    exact hsN ((H.normalizes_iff hLtw.1 hJ'P.1 hJ's).mpr (Or.inl hc))
  · intro hc
    exact hsN ((H.normalizes_iff hLtw.1 hJ'P.1 hJ's).mpr (Or.inr hc))

theorem exists_normalizes (H : Hyp Ω) (F : WFrame Ω W K s g₀) {J : Subgroup G} (hJ : J ∈ Ω)
    (hJs : IsUniqueInvolution J s) :
    ∃ u : G, (u = g₀ * (s * g₀ * s⁻¹) ∨ u = g₀ * (s * g₀ * s⁻¹)⁻¹) ∧
      u ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp F.hK
  have hzKD : zK ∈ zGroup Ω := Subgroup.subset_closure ⟨K, F.hK, hzK⟩
  have hg0K : g₀ ∈ K := (Subgroup.mem_inf.mp F.hg₀).1
  have hg0sq : g₀ * g₀ = zK := by
    have hy : g₀ * g₀ ∈ K := K.mul_mem hg0K hg0K
    have hyy : (g₀ * g₀) * (g₀ * g₀) = 1 := by
      have h4 : g₀ ^ 4 = 1 := by rw [← F.hg₀4]; exact pow_orderOf_eq_one g₀
      calc (g₀ * g₀) * (g₀ * g₀) = g₀ ^ 4 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
        _ = 1 := h4
    have hy1 : g₀ * g₀ ≠ 1 := by
      intro h
      have h2 : g₀ ^ 2 = 1 := by rw [pow_two]; exact h
      have hd := orderOf_dvd_of_pow_eq_one h2
      rw [F.hg₀4] at hd
      norm_num at hd
    exact (hzK.unique _ hy hyy).resolve_left hy1
  have hcomm : s * zK = zK * s := H.endHyp.zGroup_comm H.perp9 s F.hs zK hzKD
  have hg1sq : (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = zK := by
    calc (s * g₀ * s⁻¹) * (s * g₀ * s⁻¹) = s * (g₀ * g₀) * s⁻¹ := by group
      _ = s * zK * s⁻¹ := by rw [hg0sq]
      _ = zK := by rw [hcomm]; group
  have hzKinv : zK⁻¹ = zK := inv_eq_of_mul_eq_one_right hzK.sq
  have hg1inv : (s * g₀ * s⁻¹)⁻¹ = (s * g₀ * s⁻¹) * zK := by
    have h1 : (s * g₀ * s⁻¹) * ((s * g₀ * s⁻¹) * zK) = 1 := by
      calc (s * g₀ * s⁻¹) * ((s * g₀ * s⁻¹) * zK)
          = ((s * g₀ * s⁻¹) * (s * g₀ * s⁻¹)) * zK := (mul_assoc _ _ _).symm
        _ = zK * zK := by rw [hg1sq]
        _ = 1 := hzK.sq
    exact (eq_inv_of_mul_eq_one_right h1).symm
  have hzN : zK ∉ Subgroup.normalizer (J : Set G) := by
    intro h
    exact F.hsK (mem_normalizer_iff_conjSub_eq.mp
      ((H.endHyp.mem_normalizer_comm H.perp9 F.hK hJ hzK hJs).mpr h))
  obtain ⟨a, haD, haM, hab⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp (H.relIndex_inf_normalizer hJ)
  have hzKM : zK ∉ zGroup Ω ⊓ Subgroup.normalizer (J : Set G) :=
    fun h => hzN (Subgroup.mem_inf.mp h).2
  have hzaM : zK * a ∈ zGroup Ω ⊓ Subgroup.normalizer (J : Set G) :=
    (hab zK hzKD).resolve_right hzKM
  have hu1D : g₀ * (s * g₀ * s⁻¹) ∈ zGroup Ω := (mem_zGroup H F (Or.inl rfl) hzK).1
  rcases hab _ hu1D with h | h
  ·
    have hsplit : g₀ * (s * g₀ * s⁻¹) * zK = (g₀ * (s * g₀ * s⁻¹) * a) * (zK * a)⁻¹ := by
      rw [mul_inv_rev, hzKinv]
      group
    have hmem : g₀ * (s * g₀ * s⁻¹) * zK ∈ zGroup Ω ⊓ Subgroup.normalizer (J : Set G) := by
      rw [hsplit]
      exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ hzaM)
    exact ⟨g₀ * (s * g₀ * s⁻¹) * zK, Or.inr (by rw [hg1inv]; group),
      (Subgroup.mem_inf.mp hmem).2⟩
  · exact ⟨g₀ * (s * g₀ * s⁻¹), Or.inl rfl, (Subgroup.mem_inf.mp h).2⟩

end WFrame

end End18

namespace AE8End

variable {Ω : Set (Subgroup G)} {u : G}

theorem SectData.oneClass_of (H : End18.Hyp Ω) (hu1 : u ≠ 1)
    (hadj : ∃ R ∈ Generic.centMembers Ω u, ∃ T ∈ Generic.centMembers Ω u,
      T ∈ omegaStarNbr Ω R ∧ T ∉ KPerp Ω R) :
    ∀ L ∈ Generic.centMembers Ω u, ∀ L' ∈ Generic.centMembers Ω u,
      ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x L = L' := by
  obtain ⟨R, hRP, T, hTP, -, hTK⟩ := hadj
  have hR : R ∈ Ω := hRP.1
  have hT : T ∈ Ω := hTP.1
  have hTV : T ∉ twinSet Ω R := by
    rwa [EndHyp.kPerp_eq_twinSet_of_perp9 H.endHyp H.perp9 hR] at hTK
  rcases StarHyp.sectionConcl_centMembers H.endHyp.toStarHyp hu1 with
    ⟨-, hcomm⟩ | ⟨htrans, -, -⟩
  ·
    have hRT : ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x R = T := by
      by_contra hcon
      exact SectData.ae8a_not_commutes H hR hT hTV (hcomm R hRP T hTP hcon)
    have hall : ∀ L ∈ Generic.centMembers Ω u,
        ∃ x ∈ pSpan (Generic.centMembers Ω u), conjSub x L = R := by
      intro L hL
      by_contra hcon
      have hLR : Commutes L R := hcomm L hL R hRP hcon
      have hLT : Commutes L T := hcomm L hL T hTP fun h =>
        hcon (SectData.ae8a_conj_trans h (SectData.ae8a_conj_symm hRT))
      obtain ⟨zL, hzL⟩ := (H.endHyp.thmD.hyp.omega1 L hL.1).1
      obtain ⟨zR, hzR⟩ := (H.endHyp.thmD.hyp.omega1 R hR).1
      obtain ⟨zT, hzT⟩ := (H.endHyp.thmD.hyp.omega1 T hT).1
      have e1 : zL = zR := H.perp9 L hL.1 R hR hLR zL zR hzL hzR
      have e2 : zL = zT := H.perp9 L hL.1 T hT hLT zL zT hzL hzT
      have e3 : zR = zT := e1.symm.trans e2
      exact hTV ⟨hT, zR, hzR, by rw [e3]; exact hzT⟩
    intro L hL L' hL'
    exact SectData.ae8a_conj_trans (hall L hL) (SectData.ae8a_conj_symm (hall L' hL'))
  · exact htrans

theorem SectData.ncard_twin_of (H : End18.Hyp Ω) (hu1 : u ≠ 1)
    (hadj : ∃ R ∈ Generic.centMembers Ω u, ∃ T ∈ Generic.centMembers Ω u,
      T ∈ omegaStarNbr Ω R ∧ T ∉ KPerp Ω R)
    (htw : ∃ L ∈ Generic.centMembers Ω u,
      (twinSet Ω L ∩ Generic.centMembers Ω u).ncard = 2) :
    ∀ L ∈ Generic.centMembers Ω u, (twinSet Ω L ∩ Generic.centMembers Ω u).ncard = 2 := by
  obtain ⟨L₀, hL₀, h2⟩ := htw
  intro L hL
  obtain ⟨x, hx, hxL⟩ := SectData.oneClass_of H hu1 hadj L₀ hL₀ L hL
  have hxc : Commute x u :=
    Subgroup.mem_centralizer_singleton_iff.mp (pSpan_le (fun _ hM => hM.2) hx)
  have hpre : (fun M : Subgroup G => conjSub x M) ⁻¹' (twinSet Ω L ∩ Generic.centMembers Ω u)
      = twinSet Ω L₀ ∩ Generic.centMembers Ω u := by
    ext M
    simp only [Set.mem_preimage, Set.mem_inter_iff]
    constructor
    · rintro ⟨h1, h2'⟩
      refine ⟨?_, (SectData.ae8a_conjSub_mem_iff H hxc).mp h2'⟩
      have h3 : conjSub x⁻¹ L = L₀ := by rw [← hxL]; exact conjSub_inv_conjSub x L₀
      have h4 := SectData.ae8a_twin_conj H x⁻¹ h1
      rwa [conjSub_inv_conjSub x M, h3] at h4
    · rintro ⟨h1, h2'⟩
      refine ⟨?_, (SectData.ae8a_conjSub_mem_iff H hxc).mpr h2'⟩
      have h4 := SectData.ae8a_twin_conj H x h1
      rwa [hxL] at h4
  have hsub : twinSet Ω L ∩ Generic.centMembers Ω u ⊆
      Set.range (fun M : Subgroup G => conjSub x M) := fun N _ =>
    ⟨conjSub x⁻¹ N, conjSub_conjSub_inv x N⟩
  calc (twinSet Ω L ∩ Generic.centMembers Ω u).ncard
      = ((fun M : Subgroup G => conjSub x M) ⁻¹'
          (twinSet Ω L ∩ Generic.centMembers Ω u)).ncard :=
        (Set.ncard_preimage_of_injective_subset_range (conjSub_injective x) hsub).symm
    _ = (twinSet Ω L₀ ∩ Generic.centMembers Ω u).ncard := by rw [hpre]
    _ = 2 := h2

structure SectFrame (Ω : Set (Subgroup G)) (u : G) : Prop extends SectData Ω u where
  cent : ∀ L ∈ Ω, u ∈ Subgroup.normalizer (L : Set G) →
    ∃ R ∈ Generic.centMembers Ω u, R ∈ twinSet Ω L
  inD0 : ∃ K ∈ Ω, ∃ s ∈ zGroup Ω, conjSub s K ≠ K ∧ u ∈ K ⊔ conjSub s K

section FrameCert


theorem exists_sectFrame (H : End18.Hyp Ω) : ∃ u : G, SectFrame Ω u := by
  obtain ⟨W, K, J, s, g₀, hJ, hJs, F⟩ := End18.exists_wFrame H
  obtain ⟨u, hu, huJ⟩ := End18.WFrame.exists_normalizes H F hJ hJs
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution H.endHyp.thmD.hyp F.hK
  obtain ⟨hudz, -, huKs, hu_nz⟩ := End18.WFrame.mem_zGroup H F hu hzK
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hu_nz (Subgroup.one_mem _)
  have hadj := End18.WFrame.adj H F hu
  have htw := End18.WFrame.twin H F hu
  have hP2 : ∀ L ∈ Generic.centMembers Ω u,
      (twinSet Ω L ∩ Generic.centMembers Ω u).ncard ≤ 2 :=
    fun L hL => (SectData.ncard_twin_of H hu1 hadj htw L hL).le
  refine ⟨u, ⟨⟨hudz, hu1, End18.WFrame.mem_pSpan H F hu hP2, hadj,
    End18.WFrame.bad H F hu hP2 hJ hJs huJ, htw⟩,
    fun L hL huL => End18.WFrame.exists_twin_cent H F hu hP2 hL huL,
    ⟨K, F.hK, s, F.hs, F.hsK, huKs⟩⟩⟩

end FrameCert

end AE8End

end CFSG.ClassicalInvolution.Q3.Sec13
