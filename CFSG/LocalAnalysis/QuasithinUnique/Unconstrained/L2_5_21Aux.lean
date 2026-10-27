module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6Good
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Bridge
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_21Setup

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Basic

variable {G : Type} [Group G]

theorem SBar.exists_sq_ne_one {S A : Subgroup G} {P : Type} [Group P] [Finite P] {π : G → P}
    {R : Subgroup P} (h : SBar S A π R) {Q : Subgroup G} (hQS : Q ≤ S) (hQA : Q ⊓ A = ⊥)
    (hQ8 : 8 ≤ Nat.card Q) : ∃ ρ ∈ Q, ρ ∈ h.Rt ∧ ρ * ρ ≠ 1 := by
  have hcard : Nat.card (h.img Q) = Nat.card Q := h.card_img hQS hQA
  have h1 := DS.card_le_mul_inf_of_index_two h.ds.index_two (h.img Q)
  by_contra hno
  push Not at hno
  have hsq : ∀ r ∈ h.img Q ⊓ R, r * r = 1 := by
    intro r hr
    obtain ⟨x, hxQ, hxS, rfl⟩ := h.mem_img.mp hr.1
    have hxR : x ∈ h.Rt := h.mem_Rt.mpr ⟨hxS, hr.2⟩
    have := hno x hxQ hxR
    rw [← h.mul x hxS x hxS, this, h.pi_one]
  have h2 := h.ds.card_le_two_of_sq (h.img Q ⊓ R) inf_le_right hsq
  omega

end Basic

section Cone

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Facts258.eight_le_card_SK (h : Facts258 N) : 8 ≤ Nat.card N.SK := by
  rcases h.SK_shape with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have : NeZero n := ⟨by omega⟩
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, DihedralGroup.card]
    omega
  · rw [Nat.card_congr e.toEquiv, CFSG.Semidihedral.card 4 (by norm_num)]
    norm_num

end Cone

section Commutator

variable {G : Type} [Group G]

theorem inv_conj_mem_commutator {S : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (S : Set G))
    {c : G} (hc : c ∈ ⁅S, S⁆) : x⁻¹ * c * x ∈ ⁅S, S⁆ := by
  have hmap : S.map (MulAut.conj x⁻¹).toMonoidHom = S := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨s, hs', rfl⟩
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (S : Set G)).inv_mem hx) s).mp hs'
      simpa using this
    · intro hy
      refine ⟨x * y * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx y).mp hy, ?_⟩
      show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y
      group
  have h1 := Subgroup.map_commutator S S (MulAut.conj x⁻¹).toMonoidHom
  rw [hmap] at h1
  have h2 : (MulAut.conj x⁻¹).toMonoidHom c ∈ ⁅S, S⁆ := by
    rw [← h1]; exact Subgroup.mem_map_of_mem _ hc
  simpa using h2

end Commutator

section CharTwoK

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {t zK : G}

theorem Lv2520.charTwo_K_inf_centralizer_conj (h : Lv2520 N t zK) {g : G}
    (hg : g⁻¹ * N.z * g ∈ N.S) :
    CharTwo (N.K ⊓ Subgroup.centralizer ({g⁻¹ * N.z * g} : Set G)) := by
  set u : G := g⁻¹ * N.z * g with hu
  have hK0 : N.K0 = N.K := h.concl2520
  have hKH := h.hKH
  have hf := h.facts2511
  have hz2 : N.z * N.z = 1 := by have := N.tuple.z_sq; rwa [sq] at this
  have hz1 : N.z ≠ 1 := N.tuple.z_ne_one
  have htS : t ∈ N.S := hf.t_mem_center.1
  have htu : u * t = t * u := Subgroup.mem_centralizer_iff.mp hf.t_mem_center.2 u hg
  have hzT : N.z ∈ centerOf T := N.tuple.z_mem
  have hTz : T ≤ Subgroup.centralizer ({N.z} : Set G) := fun w hw =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hzT.2 w hw)
  have hzpow2 : IsPGroup 2 ↥(Subgroup.zpowers N.z) :=
    hs.setting.isPGroup.to_le (Subgroup.zpowers_le.mpr (N.tuple.center_le hzT |> fun hzS =>
      N.S_le_T hzS))
  have hloc : IsTwoLocal (Subgroup.centralizer ({N.z} : Set G)) :=
    ⟨Subgroup.zpowers N.z, fun h1 => hz1 (Subgroup.zpowers_eq_bot.mp h1), hzpow2,
      (normalizer_zpowers_eq_centralizer hz2).symm⟩
  have hCzM : Subgroup.centralizer ({N.z} : Set G) ≤ M :=
    hs.setting.le_of_isTwoLocal_of_isSylowTwoOf_M hs.setting.isSylowTwoOf_M hloc hTz
  have hzM : Subgroup.zpowers N.z ≤ M :=
    (Subgroup.zpowers_le.mpr (N.tuple.center_le hzT |> fun hzS => hs.setting.le (N.S_le_T hzS)))
  have hCharz : CharTwo (Subgroup.centralizer ({N.z} : Set G)) := by
    have := hs.setting.charTwo.inf_centralizer hzM hzpow2
    rwa [centralizer_zpowers_eq, inf_eq_right.mpr hCzM] at this
  have hCharu : CharTwo (Subgroup.centralizer ({u} : Set G)) := by
    rw [hu, centralizer_conj_singleton]
    exact (charTwo_map_equiv_iff (MulAut.conj g⁻¹) _).mpr hCharz
  have htpow2 : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    N.tuple.sylow.isPGroup.to_le (Subgroup.zpowers_le.mpr htS)
  have htC : Subgroup.zpowers t ≤ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_singleton_iff.mpr htu.symm
  have hChartu : CharTwo (Subgroup.centralizer ({u} : Set G) ⊓
      Subgroup.centralizer ({t} : Set G)) := by
    have := hCharu.inf_centralizer htC htpow2
    rwa [centralizer_zpowers_eq] at this
  have hGt : Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (N.K : Set G) := by
    rw [h.concl2518.2.1]
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [hK0]; exact Subgroup.le_normalizer
    · exact N.S_le_normalizer_K hKH
    · rw [← hK0]
      exact inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hKt : N.K ≤ Subgroup.centralizer ({t} : Set G) := by
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp (N.SC_le_centralizer hf.t_mem) k (hK0 ▸ hk))
  set Y : Subgroup G :=
    Subgroup.centralizer ({u} : Set G) ⊓ Subgroup.centralizer ({t} : Set G) with hY
  have hKuY : N.K ⊓ Subgroup.centralizer ({u} : Set G) ≤ Y :=
    fun k hk => ⟨hk.2, hKt hk.1⟩
  have hYnorm : Y ≤ Subgroup.normalizer ((N.K ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :
      Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf _ _ _
      (inf_le_right.trans hGt) (inf_le_left.trans Subgroup.le_normalizer)
  exact CharTwo.of_normal hChartu hKuY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKuY).mpr hYnorm)

end CharTwoK

end CFSG.QuasithinUnique
