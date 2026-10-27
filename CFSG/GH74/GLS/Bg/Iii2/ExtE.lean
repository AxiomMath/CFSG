module

public import CFSG.GH74.GLS.Bg.Iii2.ExtA

public section

namespace CFSG.GH74.GLS.Bg.Iii2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.ABGLocalTools CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec6

variable {G : Type} [Group G] [Finite G]

theorem rrSylowProd_normal {x : G} {T : Subgroup G} (hTC : T ≤ centralizer ({x} : Set G)) :
    ∀ t ∈ T, ∀ p ∈ (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K),
      t * p * t⁻¹ ∈ (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K) := by
  intro t ht
  have hle : (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K) ≤
      (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K).comap (MulAut.conj t).toMonoidHom := by
    refine iSup₂_le fun K hK => ?_
    intro p hp
    have hK' : IsRigidRankOneComp x (cmap t K) := isRigidRankOneComp_cmap hK (hTC ht)
    have hmem : t * p * t⁻¹ ∈ T ⊓ cmap t K := by
      refine ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), mem_cmap.2 ?_⟩
      have e : t⁻¹ * (t * p * t⁻¹) * t = p := by group
      rw [e]
      exact hp.2
    exact Subgroup.mem_iSup_of_mem (cmap t K) (Subgroup.mem_iSup_of_mem hK' hmem)
  exact fun p hp => hle hp

theorem ext_of_max (hPU : PU) (hCM : CM) (h43d : II4_43d) (hquat : II4_4_quat) (hG : IsKProperSimple G)
    (h3 : 3 ≤ pRank 2 G) {x : G} (hx : orderOf x = 2) (hne : ∃ K, IsRigidRankOneComp x K)
    (hmax1 : ∀ y : G, orderOf y = 2 → (∃ J, IsRigidRankOneComp y J) → rrNum y ≤ rrNum x)
    (hmax2 : ∀ y : G, orderOf y = 2 → (∃ J, IsRigidRankOneComp y J) → rrNum y = rrNum x →
      cLog y ≤ cLog x)
    (hmax3 : ∀ y : G, orderOf y = 2 → (∃ J, IsRigidRankOneComp y J) → rrNum y = rrNum x →
      cLog y = cLog x → rrMem y ≤ rrMem x) :
    ∃ T : Subgroup G, ExtData G x T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hxT⟩ := exists_sylow_mem hx
  have hTcard : Nat.card ↥T = 2 ^ cLog x := hT.card_eq
  obtain ⟨Q, hQ⟩ := hT.isPGroup.exists_le_sylow
  have hSp : IsPGroup 2 ↥(Q : Subgroup G) := Q.isPGroup'
  have hSne : (Q : Subgroup G) ≠ ⊥ := by
    intro h
    have h1 : x ∈ (Q : Subgroup G) := hQ hxT
    rw [h, Subgroup.mem_bot] at h1
    exact ne_one_of_orderOf_eq_two hx h1
  obtain ⟨y, -, hy, hyS⟩ := exists_involution_normal hSp le_rfl
    (fun s hs p hp => (Q : Subgroup G).mul_mem ((Q : Subgroup G).mul_mem hs hp)
      ((Q : Subgroup G).inv_mem hs)) hSne
  obtain ⟨hyX, hnum, -, -⟩ := ext_core hPU hCM h43d hquat hG h3 hx hne hmax1 hT hxT hQ hy hyS
  have hcl : cLog y ≤ cLog x := hmax2 y hy hyX hnum
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hSp
  have hSC : (Q : Subgroup G) ≤ centralizer ({y} : Set G) := fun s hs => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hyS s hs).symm
  have hTS : T = (Q : Subgroup G) := by
    apply Subgroup.eq_of_le_of_card_ge hQ
    rw [hk, hTcard]
    exact Nat.pow_le_pow_right (by norm_num) ((pow_le_cLog hSC hk).trans hcl)
  have hTsyl : IsSylowOf 2 T ⊤ := by
    apply isSylowOf_of_card le_top
    rw [hTS, Subgroup.card_top]
    exact Q.card_eq_multiplicity
  obtain ⟨K₀, hK₀⟩ := hne
  obtain ⟨n, hn⟩ := hquat G hG x hx T K₀ hT (rr_pcomp hK₀) hK₀.2
  obtain ⟨z, -, hzP, -, hz1, -⟩ := quat_data ⟨n, hn⟩
  have hPne : (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K) ≠ ⊥ := by
    intro h
    have h1 : z ∈ (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K) :=
      Subgroup.mem_iSup_of_mem K₀ (Subgroup.mem_iSup_of_mem hK₀ hzP)
    rw [h, Subgroup.mem_bot] at h1
    exact hz1 h1
  obtain ⟨y₁, hy₁P, hy₁, hy₁T⟩ := exists_involution_normal hT.isPGroup
    (iSup₂_le fun K _ => inf_le_left) (rrSylowProd_normal hT.le) hPne
  obtain ⟨hyX₁, hnum₁, J₁, hJ₁, hJP₁⟩ :=
    ext_core hPU hCM h43d hquat hG h3 hx ⟨K₀, hK₀⟩ hmax1 hT hxT le_rfl hy₁ hy₁T
  have hTC₁ : T ≤ centralizer ({y₁} : Set G) := fun t ht => by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (hy₁T t ht).symm
  have hcl₁ : cLog y₁ = cLog x :=
    le_antisymm (hmax2 y₁ hy₁ hyX₁ hnum₁) (pow_le_cLog hTC₁ hTcard)
  have hPle : (⨆ (K : Subgroup G) (_ : IsRigidRankOneComp x K), T ⊓ K) ≤ rigidProduct y₁ :=
    iSup₂_le fun K hK =>
      (hJP₁ K hK (T ⊓ K) (rr_sylow hK hT) (fun p hp => (hy₁T p hp.1).symm)).trans
        (le_sSup (hJ₁ K hK))
  have hmem : y₁ ∈ rigidProduct y₁ := hPle hy₁P
  have h1 : rrMem x = 1 :=
    le_antisymm (rrMem_le_one x)
      ((rrMem_eq_one_iff.2 hmem).symm.le.trans (hmax3 y₁ hy₁ hyX₁ hnum₁ hcl₁))
  exact ⟨T, hx, ⟨K₀, hK₀⟩, hTsyl, hT.le, hxT, rrMem_eq_one_iff.1 h1⟩

end CFSG.GH74.GLS.Bg.Iii2
