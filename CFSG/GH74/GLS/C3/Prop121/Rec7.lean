module

public import CFSG.GH74.GLS.C3.Prop121.Rec5
public import CFSG.GH74.GLS.C3.Prop121.Rec7Abs
public import CFSG.GH74.GLS.C3.Prop121.CentK7

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS

section Config

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

theorem recog_seven_of_card
    (hC : pRank 2 G ≤ 4) (h : IsAConfig 7 x K T Q S a) {t u g : G}
    (hS : Stage3Loc 7 x K Q t u g) (hcard : Nat.card ↥(centralizer ({t} : Set G)) = 60480) :
    ∃ L : Subgroup G, (∀ l ∈ L, l * t = t * l) ∧
      (∀ c : G, c * t = t * c → ∃ i : ℤ, ∃ l ∈ L, c = t ^ i * l) ∧
      (∀ i : ℤ, t ^ i ∈ L → t ^ i = 1) ∧ Nonempty (↥L ≃* alternatingGroup (Fin (7 + 1))) := by
  classical
  have ht3 : t ^ 3 = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hS.t_order] at this
  have ht1 : t ≠ 1 := by
    intro h1
    have := hS.t_order
    rw [h1, orderOf_one] at this
    omega
  have hc : ∀ m : ↥(centralizer ({t} : Set G)), m * tC5 t = tC5 t * m := fun m =>
    Subtype.ext (mem_centralizer_singleton_iff.1 m.2)
  have ht₃ : tC5 t ^ 3 = 1 := Subtype.ext ht3
  have ht₁ : tC5 t ≠ 1 := fun h1 => ht1 (congrArg Subtype.val h1)
  have hNn : (zpowers (tC5 t)).Normal := zpowers_normal_of_central hc
  obtain ⟨eK⟩ := hS.K_alt
  have hKC : K ≤ centralizer ({t} : Set G) :=
    fun k hk => mem_centralizer_singleton_iff.2 (hS.t_comm_K k hk).symm
  let eK₀ : ↥(K.subgroupOf (centralizer ({t} : Set G))) ≃* alternatingGroup (Fin 7) :=
    (Subgroup.subgroupOfEquivOfLe hKC).trans eK
  have hKN : ∀ k ∈ K.subgroupOf (centralizer ({t} : Set G)), k ∈ zpowers (tC5 t) → k = 1 := by
    intro k hk hkN
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hkN
    have hkG : (k : G) = t ^ i := by rw [← hi]; rfl
    have hkK : (k : G) ∈ K := Subgroup.mem_subgroupOf.1 hk
    have h1 : (k : G) = 1 := by
      refine TU.center_K_trivial (n := 7) (by norm_num) eK hkK (fun k' hk' => ?_)
      rw [hkG]
      exact ((show Commute t k' from hS.t_comm_K k' hk').zpow_left i).eq
    exact Subtype.ext h1
  have hcent : ∀ r : ↥(centralizer ({t} : Set G)),
      (∀ k ∈ K.subgroupOf (centralizer ({t} : Set G)), r * k = k * r) → r ∈ zpowers (tC5 t) := by
    intro r hr
    have h1 := centralizer_K_inf_centralizer_t_seven hC h hS (r : G)
      (fun k hk => congrArg Subtype.val
        (hr ⟨k, hKC hk⟩ (Subgroup.mem_subgroupOf.2 hk)))
      (mem_centralizer_singleton_iff.1 r.2)
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h1
    exact mem_zpowers_iff.2 ⟨i, Subtype.ext hi⟩
  obtain ⟨L₀, hL0inf, hL0sup, ⟨eL0⟩⟩ := exists_complement_alt8 hc ht₃ ht₁ hcard eK₀ hKN hcent
  refine ⟨L₀.map (centralizer ({t} : Set G)).subtype, ?_, ?_, ?_,
    ⟨(Subgroup.equivMapOfInjective L₀ (centralizer ({t} : Set G)).subtype
      (centralizer ({t} : Set G)).subtype_injective).symm.trans eL0⟩⟩
  · rintro _ ⟨l₀, -, rfl⟩
    exact mem_centralizer_singleton_iff.1 l₀.2
  · intro c hct
    let cC : ↥(centralizer ({t} : Set G)) := ⟨c, mem_centralizer_singleton_iff.2 hct⟩
    have hcm : cC ∈ L₀ ⊔ zpowers (tC5 t) := by rw [hL0sup]; exact Subgroup.mem_top _
    obtain ⟨y, hy, m, hm, hym⟩ := Subgroup.mem_sup_of_normal_right.1 hcm
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hm
    refine ⟨i, y, ⟨y, hy, rfl⟩, ?_⟩
    have h1 : (y : G) * (t ^ i) = c := by
      have := congrArg Subtype.val hym
      rw [← hi] at this
      exact this
    rw [← h1]
    have : Commute (t ^ i) (y : G) := by
      have hyt : Commute (y : G) t := mem_centralizer_singleton_iff.1 y.2
      exact hyt.symm.zpow_left i
    exact this.eq.symm
  · intro i hi
    obtain ⟨l₀, hl₀, hl₀t⟩ := hi
    have h1 : l₀ = tC5 t ^ i := Subtype.ext hl₀t
    have h2 : l₀ ∈ zpowers (tC5 t) := by
      rw [h1]
      exact Subgroup.zpow_mem _ (mem_zpowers (tC5 t)) i
    have h3 : l₀ ∈ L₀ ⊓ zpowers (tC5 t) := ⟨hl₀, h2⟩
    rw [hL0inf, Subgroup.mem_bot] at h3
    calc t ^ i = (centralizer ({t} : Set G)).subtype l₀ := hl₀t.symm
      _ = (centralizer ({t} : Set G)).subtype 1 := by rw [h3]
      _ = 1 := map_one _

end Config

@[expose] def S_card7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], pRank 2 G ≤ 4 →
    ∀ (x : G) (K T Q S : Subgroup G) (a : G), IsAConfig 7 x K T Q S a →
      IsApproxTo G (alternatingGroup (Fin (7 + 4))) →
        ∀ t u g : G, Stage3Loc 7 x K Q t u g → Nat.card ↥(centralizer ({t} : Set G)) = 60480

theorem s_recog_seven_of_card
    (h7 : S_card7) : S_recog 7 :=
  fun _ _ _ hC _ _ _ _ _ _ h hap _ _ _ hS =>
    recog_seven_of_card hC h hS (h7 _ hC _ _ _ _ _ _ h hap _ _ _ hS)

theorem s_prop121_cfg_of_card7
    (h7 : S_card7) : S_prop121_cfg :=
  s_prop121_cfg_of_recog_seven (s_recog_seven_of_card h7)

end CFSG.GH74.GLS.C3.Prop121
