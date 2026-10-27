module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YAG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YTdict1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.YFRelG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Q8Q8Proof

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank.G2Three.Sec2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem closure_pair_le_A (s : Setting3 G L) {x y : G}
    (hx : x ∈ ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂} : Set G))
    (hy : y ∈ ({s.fr.a₁, s.fr.b₁, s.fr.a₂, s.fr.b₂} : Set G)) :
    (closure {x, y} : Subgroup G) ≤ s.fr.A := by
  rw [Subgroup.closure_le]
  intro z hz
  rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl
  · exact Subgroup.subset_closure hx
  · exact Subgroup.subset_closure hy

private theorem sup_U_V (s : Setting3 G L) :
    (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ⊔ closure {s.fr.a₂, s.fr.b₂} = s.fr.A := by
  rw [SFrame.A, ← Subgroup.closure_union]
  congr 1
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem commute_UV (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) :
    ∀ u ∈ (closure {s.fr.a₁, s.fr.b₁} : Subgroup G),
      ∀ v ∈ (closure {s.fr.a₂, s.fr.b₂} : Subgroup G), Commute u v := by
  have hsrel := s3_srel hS hZ s
  have hgen : ∀ x ∈ ({s.fr.a₁, s.fr.b₁} : Set G),
      ∀ y ∈ ({s.fr.a₂, s.fr.b₂} : Set G), Commute x y := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact commutatorElement_eq_one_iff_commute.mp hsrel.a1a2
    · exact commutatorElement_eq_one_iff_commute.mp hsrel.a1b2
    · exact commutatorElement_eq_one_iff_commute.mp hsrel.b1a2
    · exact commutatorElement_eq_one_iff_commute.mp hsrel.b1b2
  intro u hu
  refine Subgroup.closure_induction
    (p := fun u _ => ∀ v ∈ (closure {s.fr.a₂, s.fr.b₂} : Subgroup G), Commute u v)
    ?_ ?_ ?_ ?_ hu
  · intro x hx v hv
    exact Subgroup.closure_induction (p := fun v _ => Commute x v)
      (fun y hy => hgen x hx y hy)
      (Commute.one_right x)
      (fun y z _ _ hy hz => hy.mul_right hz)
      (fun y _ hy => hy.inv_right) hv
  · intro v _
    exact Commute.one_left v
  · intro x y _ _ hx hy v hv
    exact (hx v hv).mul_left (hy v hv)
  · intro x _ hx v hv
    exact (hx v hv).inv_left

private theorem inf_U_V_card (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) :
    Nat.card ↥((closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ⊓
      closure {s.fr.a₂, s.fr.b₂}) = 2 := by
  have hA := lfactsA_of_setting hS hZ s
  have hsrel := s3_srel hS hZ s
  have hcomm := commute_UV hS hZ s
  have hzU : s.fr.z ∈ (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) := by
    rw [SFrame.z]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hzV : s.fr.z ∈ (closure {s.fr.a₂, s.fr.b₂} : Subgroup G) := by
    rw [← hsrel.b2_sq]
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) 2
  have hZU : s.fr.Z ≤ (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ⊓
      closure {s.fr.a₂, s.fr.b₂} := by
    rw [SFrame.Z]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨hzU, hzV⟩)
  have hUVZ : (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ⊓
      closure {s.fr.a₂, s.fr.b₂} ≤ s.fr.Z := by
    intro x hx
    rw [← hA.cen_A]
    refine Subgroup.mem_inf.mpr ⟨closure_pair_le_A s (by simp) (by simp) hx.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hUc : (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ≤ centralizer ({x} : Set G) := by
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm u hu x hx.2).eq.symm
    have hVc : (closure {s.fr.a₂, s.fr.b₂} : Subgroup G) ≤ centralizer ({x} : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hcomm x hx.1 v hv).eq
    have hAc : s.fr.A ≤ centralizer ({x} : Set G) := by
      rw [← sup_U_V s]
      exact sup_le hUc hVc
    exact (Subgroup.mem_centralizer_iff.mp (hAc ha) x (Set.mem_singleton x)).symm
  rw [le_antisymm hUVZ hZU, SFrame.Z, Nat.card_zpowers, hA.z_order]

private theorem jSub_closure_pair (s : Setting3 G L) {x y : G}
    {α β : MulAut (L ⧸ center L)} (hxS : x ∈ s.fr.S) (hyS : y ∈ s.fr.S)
    (hx : ActsAs L x α) (hy : ActsAs L y β) :
    jSub L (closure {x, y} : Subgroup G) = closure {α, β} := by
  refine le_antisymm ?_ ?_
  · intro γ hγ
    rw [mem_jSub L] at hγ
    obtain ⟨g, hg, hgγ⟩ := hγ
    have key : ∀ g ∈ (closure {x, y} : Subgroup G), g ∈ s.fr.S ∧
        (∀ γ, ActsAs L g γ → γ ∈ (closure {α, β} : Subgroup (MulAut (L ⧸ center L)))) := by
      intro g hg
      refine Subgroup.closure_induction (p := fun g _ => g ∈ s.fr.S ∧
        (∀ γ, ActsAs L g γ →
          γ ∈ (closure {α, β} : Subgroup (MulAut (L ⧸ center L))))) ?_ ?_ ?_ ?_ hg
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact ⟨hxS, fun γ hγ => by
            rw [actsAs_unique L hγ hx]; exact Subgroup.subset_closure (by simp)⟩
        · exact ⟨hyS, fun γ hγ => by
            rw [actsAs_unique L hγ hy]; exact Subgroup.subset_closure (by simp)⟩
      · exact ⟨s.fr.S.one_mem, fun γ hγ => by
          rw [actsAs_unique L hγ (actsAs_one L)]; exact Subgroup.one_mem _⟩
      · intro z w _ _ hz hw
        refine ⟨s.fr.S.mul_mem hz.1 hw.1, fun γ hγ => ?_⟩
        have hβz : ActsAs L z (jOn L (s3_S_le_N s) ⟨z, hz.1⟩) :=
          jOn_actsAs L (s3_S_le_N s) ⟨z, hz.1⟩
        have hβw : ActsAs L w (jOn L (s3_S_le_N s) ⟨w, hw.1⟩) :=
          jOn_actsAs L (s3_S_le_N s) ⟨w, hw.1⟩
        rw [actsAs_unique L hγ (actsAs_mul L hβz hβw)]
        exact mul_mem (hz.2 _ hβz) (hw.2 _ hβw)
      · intro z _ hz
        refine ⟨s.fr.S.inv_mem hz.1, fun γ hγ => ?_⟩
        have hβz : ActsAs L z (jOn L (s3_S_le_N s) ⟨z, hz.1⟩) :=
          jOn_actsAs L (s3_S_le_N s) ⟨z, hz.1⟩
        rw [actsAs_unique L hγ (actsAs_inv L hβz)]
        exact inv_mem (hz.2 _ hβz)
    exact (key g hg).2 γ hgγ
  · rw [Subgroup.closure_le]
    intro γ hγ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hγ
    rcases hγ with rfl | rfl
    · exact (mem_jSub L).mpr ⟨x, Subgroup.subset_closure (by simp), hx⟩
    · exact (mem_jSub L).mpr ⟨y, Subgroup.subset_closure (by simp), hy⟩

private theorem q8_closure_pair (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {x y : G} (hxS : x ∈ s.fr.S) (hyS : y ∈ s.fr.S)
    {α β : MulAut (L ⧸ center L)} (hx : ActsAs L x α) (hy : ActsAs L y β)
    (hQ : Nonempty (↥(closure {α, β} : Subgroup (MulAut (L ⧸ center L))) ≃*
      QuaternionGroup 2)) :
    Nonempty (↥(closure {x, y} : Subgroup G) ≃* QuaternionGroup 2) := by
  have hUS : (closure {x, y} : Subgroup G) ≤ s.fr.S := by
    rw [Subgroup.closure_le]
    intro z hz
    rcases (by simpa using hz : z = x ∨ z = y) with rfl | rfl
    · exact hxS
    · exact hyS
  let hUN : (closure {x, y} : Subgroup G) ≤ normalizer (L : Set G) :=
    hUS.trans (s3_S_le_N s)
  let φ : ↥(closure {x, y} : Subgroup G) →* MulAut (L ⧸ center L) := jOn L hUN
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    have ha' := jOn_actsAs L hUN a
    have hb' := jOn_actsAs L hUN b
    rw [hab] at ha'
    exact s3_inj_on_S s hS hZ (hUS a.2) (hUS b.2) ha' hb'
  have hrange : φ.range = closure {α, β} := by
    rw [range_jOn L hUN]
    exact jSub_closure_pair s hxS hyS hx hy
  obtain ⟨eQ⟩ := hQ
  exact ⟨(MonoidHom.ofInjective hφ).trans ((MulEquiv.subgroupCongr hrange).trans eQ)⟩

private theorem q8_U (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) :
    Nonempty (↥(closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ≃* QuaternionGroup 2) := by
  obtain ⟨ha₁, hb₁, -, -, -, -⟩ := s3_actsAs_gens s
  exact q8_closure_pair hS hZ s (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) ha₁ hb₁ s.facts.2.2.2.1.2.1.1

private theorem q8_V (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) :
    Nonempty (↥(closure {s.fr.a₂, s.fr.b₂} : Subgroup G) ≃* QuaternionGroup 2) := by
  obtain ⟨-, -, ha₂, hb₂, -, -⟩ := s3_actsAs_gens s
  exact q8_closure_pair hS hZ s (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp)) ha₂ hb₂ s.facts.2.2.2.1.2.1.2.1

private theorem q8_conj_of {x : G} {H : Subgroup G}
    (hH : Nonempty (↥H ≃* QuaternionGroup 2)) :
    Nonempty (↥(conjSub x H) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := hH
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom :=
    fun a b h => (MulAut.conj x).injective h
  exact ⟨(H.equivMapOfInjective (MulAut.conj x).toMonoidHom hinj).symm.trans e⟩

private theorem card_conjSub {x : G} (H : Subgroup G) :
    Nat.card ↥(conjSub x H) = Nat.card ↥H := by
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom :=
    fun a b h => (MulAut.conj x).injective h
  exact Nat.card_congr (H.equivMapOfInjective (MulAut.conj x).toMonoidHom hinj).symm.toEquiv

private theorem commute_conj_UV (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {x : G} :
    ∀ u ∈ conjSub x (closure {s.fr.a₁, s.fr.b₁} : Subgroup G),
      ∀ v ∈ conjSub x (closure {s.fr.a₂, s.fr.b₂} : Subgroup G), Commute u v := by
  intro u hu v hv
  rw [conjSub, Subgroup.mem_map] at hu hv
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  obtain ⟨v₀, hv₀, rfl⟩ := hv
  show (MulAut.conj x).toMonoidHom u₀ * (MulAut.conj x).toMonoidHom v₀ =
    (MulAut.conj x).toMonoidHom v₀ * (MulAut.conj x).toMonoidHom u₀
  rw [← map_mul, ← map_mul, (commute_UV hS hZ s u₀ hu₀ v₀ hv₀).eq]

private theorem sup_subgroupOf_eq {P Q A : Subgroup G} (hP : P ≤ A) (hQ : Q ≤ A)
    (h : P ⊔ Q = A) : P.subgroupOf A ⊔ Q.subgroupOf A = ⊤ := by
  rw [← Subgroup.map_subtype_inj (H := A)]
  have htop : (⊤ : Subgroup A).map A.subtype = A := by
    simpa using Subgroup.map_subgroupOf_eq_of_le (H := A) (K := A) (le_refl A)
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hP,
    Subgroup.map_subgroupOf_eq_of_le hQ, h, htop]

private theorem eq_of_subgroupOf_eq {P Q A : Subgroup G} (hP : P ≤ A) (hQ : Q ≤ A)
    (h : P.subgroupOf A = Q.subgroupOf A) : P = Q := by
  have h' := (Subgroup.subgroupOf_inj (K := A)).mp h
  rwa [inf_eq_left.mpr hP, inf_eq_left.mpr hQ] at h'

private theorem isQ8Decomp_of_data {P Q A : Subgroup G} (hP : P ≤ A) (hQ : Q ≤ A)
    (hsup : P ⊔ Q = A) (hinf : Nat.card ↥(P ⊓ Q) = 2)
    (hPe : Nonempty (↥P ≃* QuaternionGroup 2))
    (hQe : Nonempty (↥Q ≃* QuaternionGroup 2))
    (hcomm : ∀ u ∈ P, ∀ v ∈ Q, u * v = v * u) :
    IsQ8Decomp (P.subgroupOf A) (Q.subgroupOf A) := by
  obtain ⟨eP⟩ := hPe
  obtain ⟨eQ⟩ := hQe
  refine ⟨⟨(Subgroup.subgroupOfEquivOfLe hP).trans eP⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hQ).trans eQ⟩, ?_,
    sup_subgroupOf_eq hP hQ hsup, ?_⟩
  · intro u hu v hv
    exact Subtype.ext (hcomm u.1 (Subgroup.mem_subgroupOf.mp hu) v.1
      (Subgroup.mem_subgroupOf.mp hv))
  · rw [show (P.subgroupOf A) ⊓ (Q.subgroupOf A) = (P ⊓ Q).subgroupOf A from by
      simp only [Subgroup.subgroupOf, Subgroup.comap_inf]]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hP)).toEquiv]
    exact hinf

private theorem conjSub_pair_le_A (s : Setting3 G L) {x : G}
    (hx : x ∈ normalizer (s.fr.A : Set G)) :
    conjSub x (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ≤ s.fr.A ∧
      conjSub x (closure {s.fr.a₂, s.fr.b₂} : Subgroup G) ≤ s.fr.A := by
  have hxA : conjSub x s.fr.A = s.fr.A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  constructor
  · rw [← hxA]; exact Subgroup.map_mono (closure_pair_le_A s (by simp) (by simp))
  · rw [← hxA]; exact Subgroup.map_mono (closure_pair_le_A s (by simp) (by simp))

private theorem isQ8Decomp_UV (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) :
    IsQ8Decomp ((closure {s.fr.a₁, s.fr.b₁} : Subgroup G).subgroupOf s.fr.A)
      ((closure {s.fr.a₂, s.fr.b₂} : Subgroup G).subgroupOf s.fr.A) := by
  refine isQ8Decomp_of_data (closure_pair_le_A s (by simp) (by simp))
    (closure_pair_le_A s (by simp) (by simp)) (sup_U_V s) (inf_U_V_card hS hZ s)
    (q8_U hS hZ s) (q8_V hS hZ s) ?_
  intro u hu v hv
  exact (commute_UV hS hZ s u hu v hv).eq

private theorem isQ8Decomp_conj (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L)))
    (s : Setting3 G L) {x : G} (hx : x ∈ normalizer (s.fr.A : Set G)) :
    IsQ8Decomp ((conjSub x (closure {s.fr.a₁, s.fr.b₁} : Subgroup G)).subgroupOf s.fr.A)
      ((conjSub x (closure {s.fr.a₂, s.fr.b₂} : Subgroup G)).subgroupOf s.fr.A) := by
  let U : Subgroup G := closure {s.fr.a₁, s.fr.b₁}
  let V : Subgroup G := closure {s.fr.a₂, s.fr.b₂}
  change IsQ8Decomp ((conjSub x U).subgroupOf s.fr.A) ((conjSub x V).subgroupOf s.fr.A)
  obtain ⟨hU₁A, hV₁A⟩ := conjSub_pair_le_A s hx
  have hxA : conjSub x s.fr.A = s.fr.A := Subgroup.mem_normalizer_iff_map_conj_eq.mp hx
  have hsup₁ : conjSub x U ⊔ conjSub x V = s.fr.A := by
    rw [conjSub, conjSub, ← Subgroup.map_sup, sup_U_V s]
    exact hxA
  have hinf₁ : Nat.card ↥(conjSub x U ⊓ conjSub x V) = 2 := by
    have hinj : Function.Injective (MulAut.conj x).toMonoidHom :=
      fun a b h => (MulAut.conj x).injective h
    have heq : conjSub x U ⊓ conjSub x V = conjSub x (U ⊓ V) := by
      rw [conjSub, conjSub, conjSub,
        ← Subgroup.map_inf_eq U V (MulAut.conj x).toMonoidHom hinj]
    rw [heq, card_conjSub, inf_U_V_card hS hZ s]
  refine isQ8Decomp_of_data hU₁A hV₁A hsup₁ hinf₁
    (q8_conj_of (q8_U hS hZ s)) (q8_conj_of (q8_V hS hZ s)) ?_
  intro u hu v hv
  exact (commute_conj_UV hS hZ s u hu v hv).eq

theorem s3_U_ne_V (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L) :
    (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) ≠ closure {s.fr.a₂, s.fr.b₂} := by
  intro h
  have hA := lfactsA_of_setting hS hZ s
  have ha₁V : s.fr.a₁ ∈ (closure {s.fr.a₂, s.fr.b₂} : Subgroup G) := by
    rw [← h]
    exact Subgroup.subset_closure (by simp)
  have hb₁U : s.fr.b₁ ∈ (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) :=
    Subgroup.subset_closure (by simp)
  have hz1 : s.fr.z = 1 := by
    have hc : Commute s.fr.b₁ s.fr.a₁ := commute_UV hS hZ s s.fr.b₁ hb₁U s.fr.a₁ ha₁V
    rw [← (s3_srel hS hZ s).comm1, commutatorElement_eq_one_iff_commute]
    exact hc.symm
  exact (orderOf_eq_prime_iff.mp hA.z_order).2 hz1

theorem s3_Q8_perm (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L)
    {x : G} (hx : x ∈ normalizer (s.fr.A : Set G)) :
    (conjSub x (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) = closure {s.fr.a₁, s.fr.b₁} ∧
      conjSub x (closure {s.fr.a₂, s.fr.b₂} : Subgroup G) = closure {s.fr.a₂, s.fr.b₂}) ∨
    (conjSub x (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) = closure {s.fr.a₂, s.fr.b₂} ∧
      conjSub x (closure {s.fr.a₂, s.fr.b₂} : Subgroup G) = closure {s.fr.a₁, s.fr.b₁}) := by
  set U : Subgroup G := closure {s.fr.a₁, s.fr.b₁} with hU
  set V : Subgroup G := closure {s.fr.a₂, s.fr.b₂} with hV
  have hUA : U ≤ s.fr.A := by rw [hU]; exact closure_pair_le_A s (by simp) (by simp)
  have hVA : V ≤ s.fr.A := by rw [hV]; exact closure_pair_le_A s (by simp) (by simp)
  have hU₁A : conjSub x U ≤ s.fr.A := by rw [hU]; exact (conjSub_pair_le_A s hx).1
  have hV₁A : conjSub x V ≤ s.fr.A := by rw [hV]; exact (conjSub_pair_le_A s hx).2
  have hdec : IsQ8Decomp (U.subgroupOf s.fr.A) (V.subgroupOf s.fr.A) := by
    rw [hU, hV]; exact isQ8Decomp_UV hS hZ s
  have hdec₁ : IsQ8Decomp ((conjSub x U).subgroupOf s.fr.A)
      ((conjSub x V).subgroupOf s.fr.A) := by
    rw [hU, hV]; exact isQ8Decomp_conj hS hZ s hx
  obtain ⟨U₀, V₀, -, huniq⟩ :=
    Sec2.lemma22_1 (↥s.fr.A) ⟨U.subgroupOf s.fr.A, V.subgroupOf s.fr.A, hdec⟩
  have h1 := huniq (U.subgroupOf s.fr.A) (V.subgroupOf s.fr.A) hdec
  have h2 := huniq ((conjSub x U).subgroupOf s.fr.A) ((conjSub x V).subgroupOf s.fr.A) hdec₁
  rcases h1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;>
    rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
  · left
    exact ⟨eq_of_subgroupOf_eq hU₁A hUA (h2a.trans h1a.symm),
      eq_of_subgroupOf_eq hV₁A hVA (h2b.trans h1b.symm)⟩
  · right
    exact ⟨eq_of_subgroupOf_eq hU₁A hVA (h2a.trans h1b.symm),
      eq_of_subgroupOf_eq hV₁A hUA (h2b.trans h1a.symm)⟩
  · right
    exact ⟨eq_of_subgroupOf_eq hU₁A hVA (h2a.trans h1b.symm),
      eq_of_subgroupOf_eq hV₁A hUA (h2b.trans h1a.symm)⟩
  · left
    exact ⟨eq_of_subgroupOf_eq hU₁A hUA (h2a.trans h1a.symm),
      eq_of_subgroupOf_eq hV₁A hVA (h2b.trans h1b.symm)⟩

theorem s3_swap (hS : HRSetting G L) (hZ : Odd (Nat.card ↥(center ↥L))) (s : Setting3 G L)
    {g : G} (hg : g ∈ s.T) (hact : ActsAs L g s.fr'.σ) :
    conjSub g (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) = closure {s.fr.a₂, s.fr.b₂} := by
  obtain ⟨ha₁, hb₁, ha₂, hb₂, -, -⟩ := s3_actsAs_gens s
  have hSN : s.T ≤ normalizer (s.fr.S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (s3_S_le_T s)).mp (s3_S_normal_T s hS)
  have hga₁S : g * s.fr.a₁ * g⁻¹ ∈ s.fr.S :=
    (Subgroup.mem_normalizer_iff.mp (hSN hg) s.fr.a₁).mp (Subgroup.subset_closure (by simp))
  have hgb₁S : g * s.fr.b₁ * g⁻¹ ∈ s.fr.S :=
    (Subgroup.mem_normalizer_iff.mp (hSN hg) s.fr.b₁).mp (Subgroup.subset_closure (by simp))
  have ha₂S : s.fr.a₂ ∈ s.fr.S := s3_A_le_S s (Subgroup.subset_closure (by simp))
  have hb₂S : s.fr.b₂ ∈ s.fr.S := s3_A_le_S s (Subgroup.subset_closure (by simp))
  have hconj_a : g * s.fr.a₁ * g⁻¹ = s.fr.a₂ := by
    have hσa := (frame_sigma_conj s.fr' s.facts.1).1
    apply s3_inj_on_S s hS hZ hga₁S ha₂S
    · have h := actsAs_mul L (actsAs_mul L hact ha₁) (actsAs_inv L hact)
      rw [hσa] at h
      exact h
    · exact ha₂
  have hconj_b : g * s.fr.b₁ * g⁻¹ = s.fr.b₂ := by
    have hσb := (frame_sigma_conj s.fr' s.facts.1).2
    apply s3_inj_on_S s hS hZ hgb₁S hb₂S
    · have h := actsAs_mul L (actsAs_mul L hact hb₁) (actsAs_inv L hact)
      rw [hσb] at h
      exact h
    · exact hb₂
  show conjSub g (closure {s.fr.a₁, s.fr.b₁} : Subgroup G) = closure {s.fr.a₂, s.fr.b₂}
  rw [conjSub, MonoidHom.map_closure, Set.image_pair]
  change closure {g * s.fr.a₁ * g⁻¹, g * s.fr.b₁ * g⁻¹} = closure {s.fr.a₂, s.fr.b₂}
  rw [hconj_a, hconj_b]

end CFSG.OddStandard.HigherRank.YamadaG23
