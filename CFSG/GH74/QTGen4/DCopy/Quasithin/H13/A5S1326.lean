module

public import CFSG.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S132
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S133

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.LieType.BorelTits
open CFSG.Blueprint

@[expose] def Stmt5_1_7_one_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L M : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    (∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) →
    quasithinIsMaxTwoLocal M → T ≤ M → L ≤ M → M ≤ Subgroup.normalizer (L : Set G) →
      Subgroup.normalizer (baum T : Set G) ≤ M

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem normalizer_baum_le_F4 (h517 : Stmt5_1_7_one_F4) :
    Subgroup.normalizer (baum T : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  h517 G T L _ S.h13.simple S.h13.nonabelian S.h13.qtke S.h13.sylow S.maximal S.h13.faithful
    ⟨2, le_rfl, S.lieModel_L⟩ S.uniqueM.1.1 S.T_le_NL Subgroup.le_normalizer le_rfl

theorem isSylowTwoOf_centralizer_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) {v : G}
    (hv : v ∈ S.V2) (hv1 : v ∉ S.V1) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({v} : Set G))
      (Subgroup.centralizer ({v} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvV : v ∈ V := S.pre_le_V _ hv

  have hψW2 : InW2 (S.frame.ψ ⟨v, hvV⟩) := by
    obtain ⟨h, hW⟩ := S.mem_pre.1 hv
    exact mem_W2.1 hW
  have hψ1 : S.frame.ψ ⟨v, hvV⟩ ≠ 1 := by
    intro h
    apply hv1
    rw [S.mem_V1]
    left
    have : (⟨v, hvV⟩ : ↥V) = 1 := S.frame.ψ.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  have hψ4 : S.frame.ψ ⟨v, hvV⟩ ≠ W4 := by
    intro h
    apply hv1
    rw [S.mem_V1]
    right
    have : (⟨v, hvV⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := S.frame.ψ.injective (by rw [h, S.psi_z])
    exact congrArg Subtype.val this
  have he : S.frame.ψ ⟨v, hvV⟩ ∈ [e01, e23] := by
    rcases W2_nonsing _ hψW2 hψ1 hψ4 with h | h <;> simp [h]

  have hmemTv : ∀ g : ↥(Subgroup.normalizer (V : Set G)), (g : G) ∈ T →
      pact (S.frame.ρ g) (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ →
        (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro g hgT hfix
    refine ⟨hgT, ?_⟩
    show (g : G) ∈ Subgroup.centralizer ({v} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := (S.conj_eq_iff g ⟨v, hvV⟩).2 hfix
    calc (g : G) * v = (g : G) * v * (g : G)⁻¹ * g := by group
      _ = v * g := by rw [this]

  have hfixTv : ∀ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) →
        pact (S.frame.ρ g) (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ := by
    intro g hg
    refine (S.conj_eq_iff g ⟨v, hvV⟩).1 ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hg.2
    show (g : G) * v * (g : G)⁻¹ = v
    rw [this]; group

  have hBTv : baum T ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_inf inf_le_left fun x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (S.baum_le_centralizer_V2 hx) v hv).symm
  have hBeq : baum T = baum (T ⊓ Subgroup.centralizer ({v} : Set G)) :=
    baum_eq_of_le hBTv inf_le_left

  obtain ⟨P, hP, hTvP⟩ := A4.exists_isSylowTwoOf_ge
    (inf_le_right : T ⊓ Subgroup.centralizer ({v} : Set G) ≤ Subgroup.centralizer ({v} : Set G))
    (S.isPGroup_T.to_le inf_le_left)
  suffices hPT : P ≤ T ⊓ Subgroup.centralizer ({v} : Set G) by
    rw [le_antisymm hTvP hPT]
    exact hP
  by_contra hPT
  obtain ⟨x, hxP, hxTv, hxN⟩ :=
    exists_mem_normalizer_not_mem hP.2.1 (lt_of_le_of_ne hTvP fun h => hPT h.ge)

  have hxB : x ∈ Subgroup.normalizer (baum T : Set G) := by
    rw [hBeq]
    exact normalizer_le_normalizer_baum _ hxN
  have hxM := S.normalizer_baum_le_F4 h517 hxB
  have hxC : x ∈ Subgroup.centralizer ({v} : Set G) := hP.1 hxP
  have hv1' : v ≠ 1 := fun h => hv1 (h ▸ Subgroup.one_mem _)
  have hxU : x ∈ Subgroup.normalizer (Subgroup.zpowers v : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute v x := (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm
    exact (hc.zpow_left k).eq
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := S.mem_normalizer_V_of_F4 h1222 hxM
    (Subgroup.zpowers_ne_bot.mpr hv1') (Subgroup.zpowers_le.mpr hvV) hxU

  have hRTv : pCoreOf 2 (L ⊔ T) ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_inf S.pCoreOf_LT_le_T fun r hr => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (S.R_sylow_CV.1 hr) v hvV).symm
  have hPCV : P ⊓ Subgroup.centralizer (V : Set G) ≤ T ⊓ Subgroup.centralizer ({v} : Set G) := by
    refine le_trans ?_ hRTv
    exact (A4.isSylowTwoOf_iff_maximal.mp S.R_sylow_CV).2.2 _ inf_le_right
      (hP.2.1.to_le inf_le_left) (le_inf (hRTv.trans hTvP) S.R_sylow_CV.1)

  set σ := S.frame.ρ ⟨x, hxV⟩ with hσdef
  have hσ8 : σ ^ 8 = 1 := by
    obtain ⟨k, hk⟩ := hP.2.1 ⟨x, hxP⟩
    refine pow_eight_of_pow_two_pow (k := k) ?_
    rw [hσdef, ← map_pow]
    have : (⟨x, hxV⟩ : ↥(Subgroup.normalizer (V : Set G))) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hσe : pact σ (S.frame.ψ ⟨v, hvV⟩) = S.frame.ψ ⟨v, hvV⟩ := by
    refine (S.conj_eq_iff ⟨x, hxV⟩ ⟨v, hvV⟩).1 ?_
    have := Subgroup.mem_centralizer_singleton_iff.mp hxC
    show x * v * x⁻¹ = v
    rw [this]; group

  have hconj : ∀ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) →
        ∃ g' : ↥(Subgroup.normalizer (V : Set G)),
          (g' : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧
            S.frame.ρ g' = σ * S.frame.ρ g * σ⁻¹ := by
    intro g hg
    refine ⟨⟨x, hxV⟩ * g * ⟨x, hxV⟩⁻¹, ?_, by rw [map_mul, map_mul, map_inv, ← hσdef]⟩
    exact (Subgroup.mem_normalizer_iff.mp hxN g).mp hg

  have key : ∃ g : ↥(Subgroup.normalizer (V : Set G)),
      (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧ S.frame.ρ g = σ := by
    by_cases hodd : ∃ (t : G) (ht : t ∈ T), (S.frame.ρ ⟨t, S.frame.T_le ht⟩).sign ≠ 1
    ·
      have hV4 : ∀ τ, InV4 τ → ∃ g : ↥(Subgroup.normalizer (V : Set G)),
          (g : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) ∧ S.frame.ρ g = τ := by
        intro τ hτ
        obtain ⟨g, hgT, hgτ⟩ := S.exists_T_of_D hodd (V4_props τ hτ).1
        refine ⟨g, hmemTv g hgT ?_, hgτ⟩
        rw [hgτ]
        exact (V4_props τ hτ).2 _ he
      have hσV4 : InV4 σ := by
        refine InV4_of_normalizes σ hσ8 _ he hσe fun τ hτ => ?_
        have hτV4 : InV4 τ := by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hτ
          rcases hτ with rfl | rfl | rfl <;> decide
        obtain ⟨g, hg, rfl⟩ := hV4 τ hτV4
        obtain ⟨g', hg', hg'ρ⟩ := hconj g hg
        rw [← hg'ρ]
        exact InV4_of_D_fix _ (S.frame.T_D g' hg'.1) _ he (hfixTv g' hg')
      exact hV4 σ hσV4
    ·
      push Not at hodd
      have hσsign : σ.sign = 1 := by
        by_contra hne
        have hT : IsSylowTwoOf T (Subgroup.normalizer (V : Set G)) :=
          isSylowTwoOf_of_le S.h13.sylow S.frame.T_le
        set f : ↥(Subgroup.normalizer (V : Set G)) →* ℤˣ := Equiv.Perm.sign.comp S.frame.ρ
        have hsurj : Function.Surjective f := by
          intro u
          rcases Int.units_eq_one_or u with rfl | rfl
          · exact ⟨1, map_one f⟩
          · refine ⟨⟨x, hxV⟩, ?_⟩
            show Equiv.Perm.sign σ = -1
            rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
            · exact absurd h hne
            · exact h
        have hidx : f.ker.index = 2 := by
          rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
            Nat.card_eq_fintype_card, Fintype.card_units_int]
        have hle : T.subgroupOf (Subgroup.normalizer (V : Set G)) ≤ f.ker := by
          intro t ht
          rw [MonoidHom.mem_ker]
          exact hodd t ht
        have := Subgroup.index_dvd_of_le hle
        rw [hidx] at this
        exact hT.2.2 this
      obtain ⟨gpa, hgpaT, hgpa⟩ := S.frame.K4_T pa (by decide)
      have hpaTv : (gpa : G) ∈ T ⊓ Subgroup.centralizer ({v} : Set G) := by
        refine hmemTv gpa hgpaT ?_
        rw [hgpa]
        exact (V4_props pa (by decide)).2 _ he
      have hσpa : σ * pa * σ⁻¹ = pa := by
        obtain ⟨g', hg', hg'ρ⟩ := hconj gpa hpaTv
        rw [hgpa] at hg'ρ
        have hK : InK4 (S.frame.ρ g') :=
          InK4_of_D_alt _ (S.frame.T_D g' hg'.1) (hodd _ hg'.1)
        rcases K4_fix_e _ hK _ he (hfixTv g' hg') with h | h
        · rw [h] at hg'ρ
          exfalso
          have : pa = 1 :=
            calc pa = σ⁻¹ * (σ * pa * σ⁻¹) * σ := by group
              _ = σ⁻¹ * 1 * σ := by rw [← hg'ρ]
              _ = 1 := by group
          exact absurd this (by decide)
        · rw [← hg'ρ, h]
      rcases eq_of_even_normalizes σ hσsign hσ8 _ he hσe hσpa with h | h
      · exact ⟨1, Subgroup.one_mem _, by rw [map_one, h]⟩
      · exact ⟨gpa, hpaTv, by rw [hgpa, h]⟩

  obtain ⟨g, hgTv, hgσ⟩ := key
  have hxg : x * (g : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have := S.frame.mem_centralizer_of_rho (⟨x, hxV⟩ * g⁻¹) (by rw [map_mul, map_inv, hgσ,
      ← hσdef, mul_inv_cancel])
    simpa using this
  have hxgP : x * (g : G)⁻¹ ∈ P := P.mul_mem hxP (P.inv_mem (hTvP hgTv))
  have := hPCV ⟨hxgP, hxg⟩
  apply hxTv
  have := (T ⊓ Subgroup.centralizer ({v} : Set G)).mul_mem this hgTv
  simpa using this

theorem isSing_of_conj_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) {g : G} {v w : ↥V}
    (hgvw : g * v * g⁻¹ = w) (hv : IsSing (S.frame.ψ v)) : IsSing (S.frame.ψ w) := by
  by_contra hw
  have hw1 : S.frame.ψ w ≠ 1 := fun h => hw (h ▸ isSing_one_W4.1)
  have hv1 : S.frame.ψ v ≠ 1 := by
    intro h
    apply hw1
    have hv1 : v = 1 := S.frame.ψ.injective (by rw [h, map_one])
    have : w = 1 := by
      apply Subtype.ext
      rw [← hgvw, hv1]
      simp
    rw [this, map_one]

  obtain ⟨σ, hσ, hσv⟩ := exists_alt_pact _ _ hv1 isSing_one_W4.2 (iff_of_true hv isSing_W4)
  obtain ⟨l, hlL, hlσ⟩ := (S.frame.image_L σ).2 hσ
  obtain ⟨σ', hσ', hσ'w⟩ := exists_alt_pact _ _ hw1 e01_props.2.1 (iff_of_false hw e01_props.2.2.2)
  obtain ⟨l', hl'L, hl'σ'⟩ := (S.frame.image_L σ').2 hσ'
  have hz : (l : G) * v * (l : G)⁻¹ = S.z := by
    have := S.psi_conj l v
    rw [hlσ, hσv, ← S.psi_z] at this
    exact congrArg Subtype.val (S.frame.ψ.injective this)
  have hw'V : (l' : G) * w * (l' : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp l'.2 w).mp w.2
  have hψw' : S.frame.ψ ⟨(l' : G) * w * (l' : G)⁻¹, hw'V⟩ = e01 := by
    rw [S.psi_conj l' w, hl'σ', hσ'w]

  have hhz : ((l' : G) * g * (l : G)⁻¹) * S.z * ((l' : G) * g * (l : G)⁻¹)⁻¹ =
      (l' : G) * w * (l' : G)⁻¹ := by
    rw [← hz, ← hgvw]
    group

  have hw'2 : (l' : G) * w * (l' : G)⁻¹ ∈ S.V2 :=
    S.mem_pre.2 ⟨hw'V, by rw [hψw']; exact mem_W2.2 e01_props.1⟩
  have hw'1 : (l' : G) * w * (l' : G)⁻¹ ∉ S.V1 := by
    intro h
    rcases S.mem_V1.1 h with h1 | h1
    · have : (⟨_, hw'V⟩ : ↥V) = 1 := Subtype.ext h1
      rw [this, map_one] at hψw'
      exact e01_props.2.1 hψw'.symm
    · have : (⟨_, hw'V⟩ : ↥V) = ⟨S.z, S.z_mem_V⟩ := Subtype.ext h1
      rw [this, S.psi_z] at hψw'
      exact e01_props.2.2.1 hψw'.symm

  have hS1 := S.isSylowTwoOf_centralizer_F4 h1222 h517 hw'2 hw'1
  have hTz : T ≤ Subgroup.centralizer ({S.z} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := S.conj_z_of_mem_T ht
    calc t * S.z = t * S.z * t⁻¹ * t := by group
      _ = S.z * t := by rw [this]
  have hS2 := isSylowTwoOf_map_conj (isSylowTwoOf_of_le S.h13.sylow hTz)
    ((l' : G) * g * (l : G)⁻¹)
  rw [map_conj_centralizer_singleton, hhz] at hS2
  have hcard := card_eq_of_isSylowTwoOf hS1 hS2
  rw [card_map_conj] at hcard

  have hTeq : T ⊓ Subgroup.centralizer ({(l' : G) * w * (l' : G)⁻¹} : Set G) = T :=
    Subgroup.eq_of_le_of_card_ge inf_le_left hcard.ge
  apply hw'1
  refine S.mem_V1_of_fixed hw'V fun t ht => ?_
  have ht' : t ∈ Subgroup.centralizer ({(l' : G) * w * (l' : G)⁻¹} : Set G) :=
    (hTeq.ge ht).2
  rw [Subgroup.mem_centralizer_singleton_iff] at ht'
  rw [ht']
  group

end Setting

theorem input1326Two_of_F4
    (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) : Input1326Two_F4 := by
  intro G _ _ T L V S g v w hgvw
  refine ⟨S.isSing_of_conj_F4 h1222 h517 hgvw, fun hw => ?_⟩
  refine S.isSing_of_conj_F4 h1222 h517 (g := g⁻¹) (v := w) (w := v) ?_ hw
  rw [← hgvw]
  group

end CFSG.Quasithin.H13.A5
