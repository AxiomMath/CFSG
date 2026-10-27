module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSplit

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

namespace StdCfg

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem zU_mem_cent (C : StdCfg T M H S L) : C.zU ∈ centerOf (baum S) := by
  refine Subgroup.mem_inf.mpr ⟨C.U_le_R C.zU_mem, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
  have h := C.zU_central_S (baum_le_S hr)
  calc r * C.zU = (r * C.zU * r⁻¹) * r := by group
    _ = C.zU * r := by rw [h]

theorem u0_mul_zU (C : StdCfg T M H S L) : C.u0 * C.zU = ((C.iV g23w : ↥H) : G) := by
  have : C.iV g1w * C.iV StdCfg.z0V = C.iV g23w := by
    rw [← C.iV_add]
    exact congrArg C.iV (Subtype.ext g1_add_z0)
  exact congrArg Subtype.val this

theorem ZR_norm (C : StdCfg T M H S L) : T ≤ Subgroup.normalizer (centerOf (baum S) : Set G) := by
  intro t ht
  have htR : t ∈ Subgroup.normalizer (baum S : Set G) :=
    normalizer_le_normalizer_baum S (C.T_le_normalizer_S ht)
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact fun hv => conj_mem_centerOf htR hv
  · intro hv
    have := conj_mem_centerOf (inv_mem htR) hv
    rwa [show t⁻¹ * (t * v * t⁻¹) * t⁻¹⁻¹ = v by group] at this

end StdCfg

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

theorem u0_ne_zU : C.u0 ≠ C.zU := by
  intro h
  have h1 : C.iV g1w = C.iV StdCfg.z0V := Subtype.ext h
  exact g1_ne_z0 (congrArg Subtype.val (C.iV_inj X.hTC h1))

theorem ZR_eq (hR : C.u0 ∈ centerOf (baum S)) :
    centerOf (baum S) = Subgroup.zpowers C.u0 ⊔ Subgroup.zpowers C.zU := by
  apply le_antisymm
  · intro v hv
    rcases X.cent_cases hv with h | h | h | h
    · rw [h]
      exact one_mem _
    · rw [h]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · rw [h, ← C.u0_mul_zU]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  · exact sup_le (Subgroup.zpowers_le.mpr hR) (Subgroup.zpowers_le.mpr C.zU_mem_cent)

theorem T_conj_u0 (hR : C.u0 ∈ centerOf (baum S)) {t : G} (ht : t ∈ T) :
    t * C.u0 * t⁻¹ = C.u0 ∨ t * C.u0 * t⁻¹ = C.u0 * C.zU := by
  have hmem : t * C.u0 * t⁻¹ ∈ centerOf (baum S) := by
    have := (Subgroup.mem_normalizer_iff.mp (C.ZR_norm ht) C.u0).mp hR
    exact this
  rcases X.cent_cases hmem with h | h | h | h
  · exfalso
    apply X.u0_ne_one
    calc C.u0 = t⁻¹ * (t * C.u0 * t⁻¹) * t := by group
      _ = 1 := by rw [h]; group
  · exact Or.inl h
  · right
    rw [h, ← C.u0_mul_zU]
  · exfalso
    apply X.u0_ne_zU
    calc C.u0 = t⁻¹ * (t * C.u0 * t⁻¹) * t := by group
      _ = t⁻¹ * C.zU * t := by rw [h]
      _ = t⁻¹ * (C.zU * t) := by group
      _ = t⁻¹ * (t * C.zU) := by rw [← X.T_cent_z ht]
      _ = C.zU := by group

theorem exists_s : ∃ s ∈ S, s ∉ baum S ∧ s⁻¹ * C.u0 * s = C.u0 * C.zU ∧
    s * C.u0 * s⁻¹ = C.u0 * C.zU := by
  obtain ⟨s, hsS, hπ⟩ := C.exists_mem_S_pi (σ := rho13) ((mem_Dstd _).mpr rho13_mem_Dset)
  have hsH : s ∈ H := C.hcs.sylow.le hsS
  refine ⟨s, hsS, ?_, ?_, ?_⟩
  · intro hsR
    have := (X.mem_R_iff ⟨s, hsH⟩).mp hsR
    rw [hπ] at this
    exact rho13_not_mem_Eset this
  · have h1 := C.conj_iV X.hTC (⟨s, hsH⟩ : ↥H)⁻¹ g1w
    rw [map_inv, hπ, rho13_inv, vact_rho13_g1w, inv_inv] at h1
    have h2 := congrArg Subtype.val h1
    rw [C.u0_mul_zU]
    exact h2
  · have h1 := C.conj_iV X.hTC (⟨s, hsH⟩ : ↥H) g1w
    rw [hπ, vact_rho13_g1w] at h1
    have h2 := congrArg Subtype.val h1
    rw [C.u0_mul_zU]
    exact h2

theorem x_exists (hR : C.u0 ∈ centerOf (baum S)) : ∃ x ∈ T, x ∉ S ∧ x ∈ centralizerElem C.u0 := by
  obtain ⟨x₀, hx₀T, hx₀S⟩ := C.exists_mem_T_sdiff
  obtain ⟨s, hsS, -, hs1, -⟩ := X.exists_s
  have hzz : C.zU * C.zU = 1 := C.zU_mul_self
  have huu : C.u0 * C.u0 = 1 := C.u0_mul_self
  rcases X.T_conj_u0 hR hx₀T with h | h
  · refine ⟨x₀, hx₀T, hx₀S, ?_⟩
    show x₀ ∈ Subgroup.centralizer ({C.u0} : Set G)
    refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc C.u0 * x₀ = (x₀ * C.u0 * x₀⁻¹) * x₀ := by rw [h]
      _ = x₀ * C.u0 := by group
  · refine ⟨x₀ * s⁻¹, mul_mem hx₀T (inv_mem (C.hcs.le_T hsS)), ?_, ?_⟩
    · intro hx
      exact hx₀S (by simpa using mul_mem hx hsS)
    · show x₀ * s⁻¹ ∈ Subgroup.centralizer ({C.u0} : Set G)
      refine Subgroup.mem_centralizer_iff.2 fun g hg => ?_
      rw [Set.mem_singleton_iff] at hg
      subst hg
      have hz : x₀ * C.zU * x₀⁻¹ = C.zU := by
        calc x₀ * C.zU * x₀⁻¹ = C.zU * x₀ * x₀⁻¹ := by rw [← X.T_cent_z hx₀T]
          _ = C.zU := by group
      have h2 : x₀ * (C.u0 * C.zU) * x₀⁻¹ = C.u0 := by
        calc x₀ * (C.u0 * C.zU) * x₀⁻¹ = (x₀ * C.u0 * x₀⁻¹) * (x₀ * C.zU * x₀⁻¹) := by group
          _ = C.u0 := by
            rw [h, hz]
            calc C.u0 * C.zU * C.zU = C.u0 * (C.zU * C.zU) := by group
              _ = C.u0 := by rw [hzz]; group
      have h3 : (x₀ * s⁻¹) * C.u0 * (x₀ * s⁻¹)⁻¹ = C.u0 := by
        calc (x₀ * s⁻¹) * C.u0 * (x₀ * s⁻¹)⁻¹ = x₀ * (s⁻¹ * C.u0 * s) * x₀⁻¹ := by group
          _ = x₀ * (C.u0 * C.zU) * x₀⁻¹ := by rw [hs1]
          _ = C.u0 := h2
      calc C.u0 * (x₀ * s⁻¹) = ((x₀ * s⁻¹) * C.u0 * (x₀ * s⁻¹)⁻¹) * (x₀ * s⁻¹) := by rw [h3]
        _ = (x₀ * s⁻¹) * C.u0 := by group

omit X in
theorem mem_Cu_iff (x : G) : x ∈ centralizerElem C.u0 ↔ x * C.u0 * x⁻¹ = C.u0 := by
  rw [centralizerElem, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    have h1 : C.u0 * x = x * C.u0 := h C.u0 rfl
    calc x * C.u0 * x⁻¹ = C.u0 * x * x⁻¹ := by rw [h1]
      _ = C.u0 := by group
  · intro h g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    calc C.u0 * x = (x * C.u0 * x⁻¹) * x := by rw [h]
      _ = x * C.u0 := by group

theorem Tu_index (hR : C.u0 ∈ centerOf (baum S)) :
    (T ⊓ centralizerElem C.u0).relIndex T = 2 := by
  obtain ⟨s, hsS, -, -, hs2⟩ := X.exists_s
  have hsT : s ∈ T := C.hcs.le_T hsS
  have hzz : C.zU * C.zU = 1 := C.zU_mul_self
  have hz1 : C.zU ≠ 1 := C.zU_ne_one
  have hz : ∀ t ∈ T, t * C.zU * t⁻¹ = C.zU := fun t ht => by
    calc t * C.zU * t⁻¹ = C.zU * t * t⁻¹ := by rw [← X.T_cent_z ht]
      _ = C.zU := by group
  have hne : C.u0 * C.zU ≠ C.u0 := by
    intro h
    apply hz1
    have : C.u0 * C.zU = C.u0 * 1 := by rw [h, mul_one]
    exact mul_left_cancel this
  have hmem : ∀ x : ↥T, (x : G) ∈ T ⊓ centralizerElem C.u0 ↔
      (x : G) * C.u0 * (x : G)⁻¹ = C.u0 := by
    intro x
    rw [Subgroup.mem_inf, mem_Cu_iff]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_two_iff]
  refine ⟨⟨s, hsT⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf]
  rw [hmem, hmem]
  have hbs : ((b * ⟨s, hsT⟩ : ↥T) : G) = (b : G) * s := rfl
  rw [hbs]
  have hkey : (b : G) * s * C.u0 * ((b : G) * s)⁻¹ =
      ((b : G) * C.u0 * (b : G)⁻¹) * C.zU := by
    calc (b : G) * s * C.u0 * ((b : G) * s)⁻¹ = (b : G) * (s * C.u0 * s⁻¹) * (b : G)⁻¹ := by
          group
      _ = (b : G) * (C.u0 * C.zU) * (b : G)⁻¹ := by rw [hs2]
      _ = ((b : G) * C.u0 * (b : G)⁻¹) * ((b : G) * C.zU * (b : G)⁻¹) := by group
      _ = ((b : G) * C.u0 * (b : G)⁻¹) * C.zU := by rw [hz _ b.2]
  rcases X.T_conj_u0 hR b.2 with h | h
  · refine Or.inr ⟨h, fun h' => hne ?_⟩
    rw [hkey, h] at h'
    exact h'
  · refine Or.inl ⟨?_, fun h' => hne ?_⟩
    · rw [hkey, h]
      calc C.u0 * C.zU * C.zU = C.u0 * (C.zU * C.zU) := by group
        _ = C.u0 := by rw [hzz]; group
    · rw [h] at h'
      exact h'

theorem H_eq (h5 : IsAltType L 5) (hCU : Subgroup.centralizer (blockU L : Set G) = blockU L)
    (hLn : Subgroup.normalizer (blockU L : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    H = Subgroup.normalizer (blockU L : Set G) := by
  apply le_antisymm
  · intro h hh
    exact C1.mem_normalizer_blockU (C56.H_le_normalizer C.hcs C.hj hh)
  · have hHN : H ≤ Subgroup.normalizer (L : Set G) := C56.H_le_normalizer C.hcs C.hj
    obtain ⟨P⟩ := AppC.nonempty_a5pi (C56.isShort C.hcs) h5
    have hc := P.card_im_mul (A := Subgroup.normalizer (L : Set G)) le_rfl
    have hNU : Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (blockU L : Set G) =
        blockU L := by
      rw [hCU]
      exact inf_eq_right.mpr ((blockU_le_L C.hcs).trans Subgroup.le_normalizer)
    have h120 : Nat.card (P.im (Subgroup.normalizer (L : Set G))) ≤ 120 := by
      have := Subgroup.card_le_of_le
        (le_top : P.im (Subgroup.normalizer (L : Set G)) ≤ (⊤ : Subgroup (Equiv.Perm (Fin 5))))
      rw [Subgroup.card_top, card_perm_five] at this
      exact this
    have hcard : Nat.card (Subgroup.normalizer (L : Set G)) ≤ Nat.card H := by
      rw [← hc, hNU, C.card_U, X.card_H]
      omega
    have hHeqN : H = Subgroup.normalizer (L : Set G) :=
      Subgroup.eq_of_le_of_card_ge hHN hcard
    intro n hn
    rw [hHeqN]
    exact hLn hn

end Sec

end CFSG.QuasithinUnique.A5
