module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerBar
import CFSG.RankThree.PartTwo.Sec11.Wreath
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6LayerData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Img CFSG.AGLEmbedding

namespace PointData

variable {G : Type} [Group G] [Finite G] {P : Sylow 3 G} {M J : Subgroup G} {x e₂ e₃ t ρ : G}
  {s : ℤ} (hpd : PointData P M J x e₂ e₃ t ρ s) [((GLBPrimeCore 3 M).subgroupOf M).Normal]

include hpd

theorem img_Qf :
    img M (GLBPrimeCore 3 M) (Qf x e₂ e₃) =
      Qf (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M)) := by
  unfold img
  rw [hpd.Q_subgroupOf, map_Qf]

theorem sylow_bar : ∃ S : Sylow 3 (M ⧸ (GLBPrimeCore 3 M).subgroupOf M),
    (S : Subgroup _) = img M (GLBPrimeCore 3 M) (P : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPsyl : IsSylowOf 3 (P : Subgroup G) M := by
    rw [isSylowOf_iff]
    exact ⟨hpd.P_le, P.isPGroup', fun hdvd =>
      P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hpd.P_le))⟩
  obtain ⟨T, hT⟩ := hPsyl.exists_sylow_eq_subgroupOf
  refine ⟨T.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩
  rw [Sylow.coe_mapSurjective, hT]
  rfl

theorem core_bar (N : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) (hN : N.Normal)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  set O := GLBPrimeCore 3 M with hOdef
  set K : Subgroup ↥M := O.subgroupOf M with hKdef
  set π := QuotientGroup.mk' K with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective K
  set N' : Subgroup ↥M := N.comap π with hN'def
  have hN'n : N'.Normal := hN.comap π
  have hidx : N'.index = N.index := Subgroup.index_comap_of_surjective N hπs
  have h1 := Subgroup.card_mul_index N'
  have h2 := Subgroup.card_mul_index N
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hpos : 0 < N.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hcard : Nat.card N' = Nat.card N * Nat.card K := by
    have e : Nat.card N' * N.index = Nat.card N * Nat.card K * N.index := by
      calc Nat.card N' * N.index = Nat.card N' * N'.index := by rw [hidx]
        _ = Nat.card ↥M := h1
        _ = Nat.card (↥M ⧸ K) * Nat.card K := h3
        _ = Nat.card N * N.index * Nat.card K := by rw [← h2]
        _ = Nat.card N * Nat.card K * N.index := by ring
    exact Nat.eq_of_mul_eq_mul_right hpos e
  have hKc : Nat.card K = Nat.card O :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (glbPrimeCore_le 3 M)).toEquiv
  have hcop' : Nat.Coprime 3 (Nat.card (N'.map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective, hcard, hKc]
    exact Nat.Coprime.mul_right hcop (glbPrimeCore_coprime 3 M)
  have hsub : (N'.map M.subtype).subgroupOf M = N' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective N'
  have hnorm : M ≤ normalizer ((N'.map M.subtype : Subgroup G) : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N')).mp ?_
    rw [hsub]
    exact hN'n
  have hle : N'.map M.subtype ≤ O := le_glbPrimeCore (Subgroup.map_subtype_le N') hnorm hcop'
  rw [eq_bot_iff]
  intro n hn
  obtain ⟨n', rfl⟩ := hπs n
  have hn' : n' ∈ N' := hn
  have hO : (n' : G) ∈ O := hle ⟨n', hn', rfl⟩
  rw [mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hO

theorem no3_bar (hJC : J ≤ centralizer ({x} : Set G))
    (hC1 : ¬ ∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J,
      m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M)
    (N : Subgroup (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)) (hN : N.Normal) (h3 : IsPGroup 3 N)
    (hQN : Qf (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
        (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M)) ≤ N) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := hN
  apply hC1
  intro m hm q hq
  obtain ⟨S, hS⟩ := hpd.sylow_bar
  have hNS : N ≤ (S : Subgroup _) := h3.le_sylow_of_normal S
  have hqQ : q ∈ Qf x e₂ e₃ := by
    rw [hpd.Q_eq]
    exact mem_inf.mpr ⟨(mem_inf.mp hq).1, hJC (mem_inf.mp hq).2⟩
  have hqM : q ∈ M := hpd.Q_le_M hqQ
  have hmqM : m * q * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hqM) (M.inv_mem hm)
  have hqN : (QuotientGroup.mk ⟨q, hqM⟩ : M ⧸ (GLBPrimeCore 3 M).subgroupOf M) ∈ N := by
    apply hQN
    rw [← hpd.img_Qf]
    exact mk_mem_img hqQ hqM
  have hmqN : (QuotientGroup.mk ⟨m * q * m⁻¹, hmqM⟩ : M ⧸ (GLBPrimeCore 3 M).subgroupOf M) ∈ N := by
    have := hN.conj_mem _ hqN (QuotientGroup.mk ⟨m, hm⟩)
    have e : (QuotientGroup.mk ⟨m, hm⟩ : M ⧸ (GLBPrimeCore 3 M).subgroupOf M) *
        QuotientGroup.mk ⟨q, hqM⟩ * (QuotientGroup.mk ⟨m, hm⟩)⁻¹ =
        QuotientGroup.mk ⟨m * q * m⁻¹, hmqM⟩ := by
      rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    rwa [e] at this
  have hmqP := hS ▸ hNS hmqN
  obtain ⟨p, hpP, hpM, hp⟩ := mem_img_iff.mp hmqP
  have hO := (mk_eq_iff hpM hmqM).mp hp
  have e : m * q * m⁻¹ = p * (p⁻¹ * (m * q * m⁻¹)) := by group
  rw [e]
  exact mul_mem_sup hpP hO

theorem xdata (hJC : J ≤ centralizer ({x} : Set G))
    (hC1 : ¬ ∀ m ∈ M, ∀ q ∈ (P : Subgroup G) ⊓ J,
      m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M)
    (hsolv : CFSG.HallHigman.IsPSolvable 3 ↥(centralizer
      ({QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M)} :
        Set (M ⧸ (GLBPrimeCore 3 M).subgroupOf M)))) :
    XData (M ⧸ (GLBPrimeCore 3 M).subgroupOf M) (img M (GLBPrimeCore 3 M) (P : Subgroup G))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨x, hpd.x_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₂, hpd.e₂_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨e₃, hpd.e₃_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨t, hpd.t_memM⟩ : M))
      (QuotientGroup.mk' ((GLBPrimeCore 3 M).subgroupOf M) (⟨ρ, hpd.ρ_mem⟩ : M)) s := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := hpd.sylow_bar
  obtain ⟨φ⟩ := hpd.wreath
  refine ⟨hpd.xframe, ?_, ?_, ?_, mk_mem_img hpd.t_mem hpd.t_memM, ?_,
    hpd.core_bar, hpd.no3_bar hJC hC1, hsolv⟩
  · rw [isSylowOf_iff, Subgroup.relIndex_top_right, ← hS]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  · rw [card_img_of_inf hpd.P_le hpd.P_inf_O, Nat.card_congr φ.toEquiv]
    exact CFSG.RankThree.PartTwo.Sec11.card_wreath
  · rw [← hpd.img_Qf]
    exact img_mono hpd.Q_le_P
  · intro g hg hgx
    obtain ⟨g₀, hg₀P, hg₀M, rfl⟩ := mem_img_iff.mp hg
    have hc : g₀ * x * g₀⁻¹ * x⁻¹ ∈ (P : Subgroup G) ⊓ GLBPrimeCore 3 M := by
      refine mem_inf.mpr ⟨P.mul_mem (P.mul_mem (P.mul_mem hg₀P hpd.x_mem) (P.inv_mem hg₀P))
        (P.inv_mem hpd.x_mem), ?_⟩
      have hM' : g₀ * x * g₀⁻¹ * x⁻¹ ∈ M :=
        M.mul_mem (M.mul_mem (M.mul_mem hg₀M hpd.x_memM) (M.inv_mem hg₀M)) (M.inv_mem hpd.x_memM)
      rw [← mk_eq_one_iff hM']
      have e : (QuotientGroup.mk ⟨g₀ * x * g₀⁻¹ * x⁻¹, hM'⟩ :
          M ⧸ (GLBPrimeCore 3 M).subgroupOf M) =
          QuotientGroup.mk ⟨g₀, hg₀M⟩ * QuotientGroup.mk ⟨x, hpd.x_memM⟩ *
            (QuotientGroup.mk ⟨g₀, hg₀M⟩)⁻¹ * (QuotientGroup.mk ⟨x, hpd.x_memM⟩)⁻¹ := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        rfl
      rw [e]
      have hgx' : (QuotientGroup.mk ⟨g₀, hg₀M⟩ : M ⧸ (GLBPrimeCore 3 M).subgroupOf M) *
          QuotientGroup.mk ⟨x, hpd.x_memM⟩ =
          QuotientGroup.mk ⟨x, hpd.x_memM⟩ * QuotientGroup.mk ⟨g₀, hg₀M⟩ := hgx
      rw [hgx']
      group
    rw [hpd.P_inf_O, mem_bot] at hc
    have hcomm : g₀ * x = x * g₀ := by
      have := congrArg (fun z => z * x * g₀) hc
      simp only [one_mul] at this
      calc g₀ * x = g₀ * x * g₀⁻¹ * x⁻¹ * x * g₀ := by group
        _ = x * g₀ := this
    have hg₀Q : g₀ ∈ Qf x e₂ e₃ := by
      rw [hpd.Q_eq]
      exact mem_inf.mpr ⟨hg₀P, mem_centralizer_singleton_iff.mpr hcomm⟩
    rw [← hpd.img_Qf]
    exact mk_mem_img hg₀Q hg₀M

end PointData

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Layer
