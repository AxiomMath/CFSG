module

public import CFSG.LargeExtraspecial.S14SMKTransLift
public import CFSG.LargeExtraspecial.S14SMKDelta32

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module CFSG.Open CFSG.Fischer CFSG.SmithE CFSG.LargeExtraspecial.SMod20
  CFSG.RankThree.OrthogonalInvolutions

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem card_L0_ge_succ (S : Setting G) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxQ : g * S.z * g⁻¹ ∉ S.QG) (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    2 ^ (S.width + 1) ≤ Nat.card (S.L0 g) := by
  have hzM : S.z ∈ (S.conjBy g).M := mem_centralizer_singleton_iff.mpr (S.z_comm hxM).symm
  have hzQ : S.z ∉ (S.conjBy g).QG := z_not_mem_Qa S hxQ
  have hfix : (S.conjBy g).fixQt S.z =
      (S.conjBy g).clSub ((S.conjBy g).QG ⊓ centralizer ({S.z} : Set G)) := by
    by_contra h
    obtain ⟨y, -, hy⟩ := (S.conjBy g).lemma_3_2_1 hzM h
    apply hxz
    have hy' : y * S.z * y⁻¹ = S.z * (g * S.z * g⁻¹) := hy
    have e : g * S.z * g⁻¹ * S.z = y * S.z * y⁻¹ := by
      rw [hy']
      exact (S.z_comm hxM)
    rw [e]
    exact isConj_iff.mpr ⟨y, rfl⟩
  have h1 := card_centralizer_eq (S.conjBy g) S.z hzM
  rw [← hfix] at h1
  have h2 := finrank_commSpace_add_finrank_fixSpace
    ((S.conjBy g).ρ ⟨S.z, hzM⟩ : (S.conjBy g).Qt ≃ₗ[ZMod 2] (S.conjBy g).Qt)
  rw [← (S.conjBy g).fixQt_of_mem hzM, ← (S.conjBy g).commQt_of_mem hzM,
    (S.conjBy g).finrank_Qt_eq_two_mul_width, S.width_conjBy g] at h2
  have h3 := Submodule.finrank_mono ((S.conjBy g).commQt_le_fixQt hzM S.z_sq)
  have h4 : S.width ≤ finrank (ZMod 2) ((S.conjBy g).fixQt S.z) := by omega
  calc 2 ^ (S.width + 1) = 2 * 2 ^ S.width := by rw [pow_succ, mul_comm]
    _ ≤ 2 * 2 ^ finrank (ZMod 2) ((S.conjBy g).fixQt S.z) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h4)
    _ = Nat.card (S.L0 g) := h1.symm

theorem isPGroup_Lbar (S : Setting G) (g : G) : IsPGroup 2 (S.Lbar g) := by
  have h1 : IsPGroup 2 (S.L0 g) := (S.conjBy g).isPGroup_QG.to_le (S.L0_le_Qa g)
  have h2 : IsPGroup 2 ((S.L0 g).subgroupOf S.M) :=
    h1.of_equiv (subgroupOfEquivOfLe (S.L0_le_M g)).symm
  exact h2.map _

theorem conj_mem_Lbar_of_commute (S : Setting G) {g m' : G} (hm'M : m' ∈ S.M)
    (hm'x : Commute m' (g * S.z * g⁻¹)) {s : S.O} (hs : s ∈ S.Lbar g) :
    S.ρ ⟨m', hm'M⟩ * s * (S.ρ ⟨m', hm'M⟩)⁻¹ ∈ S.Lbar g := by
  obtain ⟨⟨k, hkM⟩, hkL, rfl⟩ := hs
  have hkL' : k ∈ S.L0 g := mem_subgroupOf.mp hkL
  have hcM : m' * k * m'⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hm'M hkM) (S.M.inv_mem hm'M)
  have hmL : m' * k * m'⁻¹ ∈ S.L0 g :=
    ⟨(S.conjBy g).conj_mem_QG (mem_centralizer_singleton_iff.mpr hm'x.eq) hkL'.1, hcM⟩
  refine ⟨⟨_, hcM⟩, mem_subgroupOf.mpr hmL, ?_⟩
  rw [show (⟨m' * k * m'⁻¹, hcM⟩ : S.M) = ⟨m', hm'M⟩ * ⟨k, hkM⟩ * ⟨m', hm'M⟩⁻¹ from
    Subtype.ext rfl, map_mul, map_mul, map_inv]

theorem commute_of_mem_Lbar (S : Setting G) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M) {s : S.O}
    (hs : s ∈ S.Lbar g) : s * S.ρ ⟨_, hxM⟩ = S.ρ ⟨_, hxM⟩ * s := by
  obtain ⟨⟨k, hkM⟩, hkL, rfl⟩ := hs
  have hkL' : k ∈ S.L0 g := mem_subgroupOf.mp hkL
  have hkx : k * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * k :=
    mem_centralizer_singleton_iff.mp (mem_centralizer_of_mem_Qa S hkL'.1)
  rw [← map_mul, ← map_mul]
  exact congrArg S.ρ (Subtype.ext hkx)

theorem exists_commute_eq_of_not_isConj (S : Setting G) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) {mp : S.Mbar}
    (hmp : mp * rhoM S ⟨_, hxM⟩ = rhoM S ⟨_, hxM⟩ * mp) :
    ∃ m' : S.M, Commute (m' : G) (g * S.z * g⁻¹) ∧ rhoM S m' = mp := by
  obtain ⟨m₁, rfl⟩ := exists_rhoM_eq mp
  exact exists_commute_rhoM_eq_of_not_isConj S hxM hxz m₁ hmp

theorem eight_le_card_Lbar (S : Setting G) (hw : S.width = 10) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z))
    (hl8 : finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) ≤ 8) : 8 ≤ Nat.card (S.Lbar g) := by
  have h1 := S.card_Lbar_mul g
  have h2 := card_L0_ge_succ S hxM hxQ hxz
  rw [hw] at h2
  have h3 : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ 8 := by
    rw [← card_clSub_Dl S hxQ, S.card_submodule]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Submodule.finrank_mono (clSub_Dl_le_commQt S hxM hxQ hxz)).trans hl8)
  by_contra h
  push Not at h
  have : Nat.card (S.Lbar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) < 8 * 2 ^ 8 :=
    Nat.mul_lt_mul_of_lt_of_le h h3 (by norm_num)
  omega

theorem card_le_two_of_inf_Mbar0_eq_bot (S : Setting G) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {K : Subgroup S.Mbar} (hK : IsPGroup 2 K)
    (hKM : K ⊓ Mbar0 S = ⊥) : Nat.card K ≤ 2 := by
  have : (Mbar0 S).Normal := timmesfeldFStar_normal S.Mbar
  have h1 : (Mbar0 S).relIndex K ∣ (Mbar0 S).index := relIndex_dvd_index_of_normal _ _
  have h2 : (Mbar0 S).relIndex K = Nat.card K := by
    rw [relIndex, ← inf_subgroupOf_right, inf_comm, hKM, bot_subgroupOf, index_bot]
  have h6 := (card_M_of_U6 S hw hU).1
  rw [h2] at h1
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  rw [hn] at h1 ⊢
  have h7 := h1.trans h6
  have hn1 : n ≤ 1 := by
    by_contra hn2
    push Not at hn2
    have : 2 ^ 2 ∣ 6 := (pow_dvd_pow 2 hn2).trans h7
    norm_num at this
  calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hn1
    _ = 2 := by norm_num


theorem tvP_conj_mem_of_fix (ψ : Mbar0 S ≃* T46) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) {p : Fin 693}
    (hp : piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) p = p) {m : S.Mbar}
    (hm : m ∈ (S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S) :
    tvP p * piM S ψ m * (tvP p)⁻¹ ∈ ((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ) := by
  have hpmp : piM S ψ ((ψ.symm ⟨tvP p, tvP_mem p⟩ : Mbar0 S) : S.Mbar) = tvP p := by
    rw [piM_of_mem, MulEquiv.apply_symm_apply]
  have hcomm : ((ψ.symm ⟨tvP p, tvP_mem p⟩ : Mbar0 S) : S.Mbar) * rhoM S ⟨_, hxM⟩ =
      rhoM S ⟨_, hxM⟩ * ((ψ.symm ⟨tvP p, tvP_mem p⟩ : Mbar0 S) : S.Mbar) := by
    apply piM_injective ψ
    rw [map_mul, map_mul, hpmp]
    have h1 := (isAutPerm_autPerm (mbarHom S ψ (rhoM S ⟨_, hxM⟩))).2 p
    rw [← piM_apply, hp] at h1
    calc tvP p * piM S ψ (rhoM S ⟨_, hxM⟩) = piM S ψ (rhoM S ⟨_, hxM⟩) * tvP p *
        (piM S ψ (rhoM S ⟨_, hxM⟩))⁻¹ * piM S ψ (rhoM S ⟨_, hxM⟩) := by rw [h1]
      _ = piM S ψ (rhoM S ⟨_, hxM⟩) * tvP p := by group
  obtain ⟨m', hm'x, hm'⟩ := exists_commute_eq_of_not_isConj S hxM hxz hcomm
  rw [← hm'] at hpmp
  refine ⟨rhoM S m' * m * (rhoM S m')⁻¹, ⟨mem_subgroupOf.mpr ?_, ?_⟩, ?_⟩
  · exact conj_mem_Lbar_of_commute S m'.2 hm'x (mem_subgroupOf.mp hm.1)
  · exact (timmesfeldFStar_normal S.Mbar).conj_mem _ hm.2 _
  · have e : piM S ψ (rhoM S m' * m * (rhoM S m')⁻¹) =
        piM S ψ (rhoM S m') * piM S ψ m * (piM S ψ (rhoM S m'))⁻¹ := by
      simp only [map_mul, map_inv]
    exact e.trans (congrArg (fun t => t * piM S ψ m * t⁻¹) hpmp)

theorem false_of_outer (ψ : Mbar0 S ≃* T46) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {g : G} (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxQ : g * S.z * g⁻¹ ∉ S.QG) (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z))
    (hl8 : finrank (ZMod 2) (S.commQt (g * S.z * g⁻¹)) ≤ 8)
    (hF : ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ T46 → IsPGroup 2 R →
      (∀ r ∈ R, r * piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) =
        piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) * r) →
      (∀ p : Fin 693, piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) p = p →
        ∀ r ∈ R, tvP p * r * (tvP p)⁻¹ ∈ R) →
      R = ⊥) : False := by
  have hKp : IsPGroup 2 ((S.Lbar g).subgroupOf S.Mbar) :=
    (isPGroup_Lbar S g).of_equiv (subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).symm
  have hRp : IsPGroup 2 (((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ)) :=
    (hKp.to_inf_left (K := Mbar0 S)).map _
  have hRT : ((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ) ≤ T46 := by
    rintro _ ⟨m, hm, rfl⟩
    have := piM_of_mem ψ ⟨m, hm.2⟩
    rw [show ((⟨m, hm.2⟩ : Mbar0 S) : S.Mbar) = m from rfl] at this
    rw [this]
    exact (ψ ⟨m, hm.2⟩).2
  obtain ⟨xb, hxb⟩ : ∃ xb : S.Mbar, xb = rhoM S ⟨g * S.z * g⁻¹, hxM⟩ := ⟨_, rfl⟩
  rw [← hxb] at hF
  have hRx : ∀ r ∈ ((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ),
      r * piM S ψ xb = piM S ψ xb * r := by
    rintro _ ⟨m, hm, rfl⟩
    have e : m * xb = xb * m := by
      rw [hxb]
      exact Subtype.ext (commute_of_mem_Lbar S hxM (mem_subgroupOf.mp hm.1))
    rw [← map_mul, ← map_mul, e]
  have hRn : ∀ p : Fin 693, piM S ψ xb p = p →
      ∀ r ∈ ((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ),
      tvP p * r * (tvP p)⁻¹ ∈ ((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ) := by
    rintro p hp _ ⟨m, hm, rfl⟩
    rw [hxb] at hp
    exact tvP_conj_mem_of_fix ψ hxM hxz hp hm
  have hR0 := hF _ hRT hRp hRx hRn
  have hKM : (S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S = ⊥ := by
    rw [eq_bot_iff]
    intro m hm
    have h1 : piM S ψ m ∈ ((S.Lbar g).subgroupOf S.Mbar ⊓ Mbar0 S).map (piM S ψ) :=
      ⟨m, hm, rfl⟩
    have h2 : piM S ψ m = 1 := (Subgroup.eq_bot_iff_forall _).mp hR0 _ h1
    exact (mem_bot).mpr (piM_injective ψ (h2.trans (map_one _).symm))
  have h2 := card_le_two_of_inf_Mbar0_eq_bot S hw hU hKp hKM
  rw [Nat.card_congr (subgroupOfEquivOfLe (S.Lbar_le_Mbar g)).toEquiv] at h2
  have h8 := eight_le_card_Lbar S hw hxM hxQ hxz hl8
  omega

end CFSG.LargeExtraspecial.S14.SMK
