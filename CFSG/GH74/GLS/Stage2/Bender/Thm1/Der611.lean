module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Elem
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der72a

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
open scoped commutatorElement

section L611

variable {G : Type} [Group G] [Finite G]

theorem lemma6_11_of (h61 : Prop6_1) (h610 : Lemma6_10) (h118 : IG_11_8) : Lemma6_11 := by
  intro G _ _ z k S M p hC Q X hmin
  have hp := hC.prime
  have hp2 := hC.p_ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_two hC.orderOf_z
  have hPp : IsPGroup p ↥(Op p M) := isPGroup_Op p hp M
  have hQP : Q ≤ Op p M := hmin.Q_mem.1
  have hQp : IsPGroup p ↥Q := hPp.to_le hQP
  have hQn : M ≤ normalizer (Q : Set G) := le_normalizer_QP (le_normalizer_Op p M) hmin.Q_mem
  have hzQ : z ∈ normalizer (Q : Set G) := hQn hC.z_mem
  have hexp : ∀ x ∈ Q, x ^ p = 1 := hmin.Q_mem.2.2.1
  have hnc : ¬ Q ≤ Cen z := hmin.Q_mem.2.2.2.2.2
  have hXQ : X ≤ Q := hmin.X_le
  have hRQ : ⁅Q, zpowers z⁆ ≤ Q := commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzQ)
  have hR0 : ⁅Q, zpowers z⁆ ≠ ⊥ := fun h => hnc (commutator_zpowers_eq_bot_iff.mp h)
  have hRC : Cen z ≤ normalizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := fun c hc =>
    le_normalizer_commutator_zpowers (hQn (hC.cen_le hc)) hc
  have hRN : NF z M ⁅Q, zpowers z⁆ := h61 G z k S M p hC _ (hRQ.trans hQP) hR0 hRC
  have hRz : z ∈ normalizer ((⁅Q, zpowers z⁆ : Subgroup G) : Set G) := hRC (mem_Cen_self z)
  have hRc : ⁅⁅Q, zpowers z⁆, zpowers z⁆ = ⁅Q, zpowers z⁆ :=
    commutator_zpowers_idem hC.orderOf_z hp hp2 hQp hzQ
  have hzY₀ : z ∈ normalizer ((Q ⊓ normalizer (X : Set G) : Subgroup G) : Set G) :=
    mem_normalizer_inf hzQ (Subgroup.le_normalizer hmin.X_inv)
  have hR₁Y₀ : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ≤ Q ⊓ normalizer (X : Set G) :=
    commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzY₀)
  have hR₁z : z ∈ normalizer ((⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ : Subgroup G) : Set G) :=
    le_normalizer_commutator_zpowers hzY₀ (mem_Cen_self z)
  have hR₁Q : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ≤ Q := hR₁Y₀.trans inf_le_left
  have hR₁c : ⁅⁅Q ⊓ normalizer (X : Set G), zpowers z⁆, zpowers z⁆ =
      ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ :=
    commutator_zpowers_idem hC.orderOf_z hp hp2 (hQp.to_le inf_le_left) hzY₀
  have hR₁0 : ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ≠ ⊥ := by
    intro h
    have hle : Q ⊓ normalizer (X : Set G) ≤ centralizer ((zpowers z : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hcen : X ⊔ (Q ⊓ centralizer (X : Set G)) ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
      refine sup_le ?_ ?_
      · exact (le_inf hXQ Subgroup.le_normalizer).trans hle
      · exact (inf_le_inf_left Q (Subgroup.centralizer_le_normalizer _)).trans hle
    have hcop : Nat.Coprime p (Nat.card ↥(zpowers z)) := by
      rw [Nat.card_zpowers, hC.orderOf_z]
      exact (Nat.coprime_primes hp Nat.prime_two).mpr hp2
    have hzX : zpowers z ≤ normalizer (X : Set G) := Subgroup.zpowers_le.mpr hmin.X_inv
    have := h118 G p hp (zpowers z) Q X hQp hcop (Subgroup.zpowers_le.mpr hzQ) hzX hXQ hcen
    exact hnc (this.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers z))))
  have hR₁N : ¬ NF z M ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ :=
    h610 G z k S M p hC X _ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf (hR₁Q.trans hQP) (hR₁Y₀.trans inf_le_right)) hR₁0 hR₁c
  have hcc : ¬ ⁅Q, zpowers z⁆ ≤ normalizer ((⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ : Subgroup G) : Set G) := by
    intro hRn
    apply h610 G z k S M p hC _ ⁅Q, zpowers z⁆ (hR₁Q.trans hQP) hR₁0 hR₁z hR₁N
      (le_inf (hRQ.trans hQP) hRn) hR0 hRc
    exact hRN
  have hZQ : zOf Q ≤ Q := inf_le_left
  have hZc : zOf Q ≤ centralizer (Q : Set G) := inf_le_right
  have he : zOf Q ≤ Cen z := by
    by_contra hne
    have hzZ : M ≤ normalizer ((zOf Q : Subgroup G) : Set G) := le_normalizer_zOf hQn
    have hzZ' : z ∈ normalizer ((zOf Q : Subgroup G) : Set G) := hzZ hC.z_mem
    have hQ₁le : ⁅zOf Q, zpowers z⁆ ≤ zOf Q :=
      commutator_le_left_of_normalizes (Subgroup.zpowers_le.mpr hzZ')
    have hQ₁0 : ⁅zOf Q, zpowers z⁆ ≠ ⊥ := fun h => hne (commutator_zpowers_eq_bot_iff.mp h)
    have hQ₁C : Cen z ≤ normalizer ((⁅zOf Q, zpowers z⁆ : Subgroup G) : Set G) := fun c hc =>
      le_normalizer_commutator_zpowers (hzZ (hC.cen_le hc)) hc
    have hQ₁N : NF z M ⁅zOf Q, zpowers z⁆ :=
      h61 G z k S M p hC _ ((hQ₁le.trans hZQ).trans hQP) hQ₁0 hQ₁C
    have hQ₁c : ⁅⁅zOf Q, zpowers z⁆, zpowers z⁆ = ⁅zOf Q, zpowers z⁆ :=
      commutator_zpowers_idem hC.orderOf_z hp hp2 (hQp.to_le hZQ) hzZ'
    have hZX : zOf Q ≤ normalizer (X : Set G) :=
      hZc.trans ((Subgroup.centralizer_le (fun x hx => hXQ hx)).trans (Subgroup.centralizer_le_normalizer _))
    exact h610 G z k S M p hC X _ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
      (le_inf ((hQ₁le.trans hZQ).trans hQP) (hQ₁le.trans hZX)) hQ₁0 hQ₁c hQ₁N
  refine ⟨?_, hR₁N, hcc, ?_, he, ?_⟩
  ·
    have hnotle : ¬ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ ≤ Cen z := by
      intro h
      have h0 := commutator_zpowers_eq_bot_iff.mpr h
      rw [hR₁c] at h0
      exact hR₁0 h0
    obtain ⟨a, haR, ha1, hainv⟩ := exists_inverted hz2 hR₁z hnotle
    have haQ : a ∈ Q := hR₁Q haR
    have hap : a ^ p = 1 := hexp a haQ
    have hY₁R : zpowers a ≤ ⁅Q ⊓ normalizer (X : Set G), zpowers z⁆ := Subgroup.zpowers_le.mpr haR
    have hY₁c : ⁅zpowers a, zpowers z⁆ = zpowers a := commutator_zpowers_eq_of_inverts hp hp2 hap hainv
    have hY₁z : z ∈ normalizer ((zpowers a : Subgroup G) : Set G) := mem_normalizer_zpowers_of_inv hainv
    have hY₁0 : zpowers a ≠ ⊥ := by
      intro h
      apply ha1
      have : a ∈ zpowers a := Subgroup.mem_zpowers a
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have hY₁N : ¬ NF z M (zpowers a) :=
      h610 G z k S M p hC X _ (hXQ.trans hQP) hmin.X_ne hmin.X_inv hmin.X_not
        (le_inf ((hY₁R.trans hR₁Q).trans hQP) (hY₁R.trans (hR₁Y₀.trans inf_le_right))) hY₁0 hY₁c
    have hcardY₁ : Nat.card ↥(zpowers a) = p := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hap ha1
    have hXp : IsPGroup p ↥X := hQp.to_le hXQ
    have hle1 : Nat.card ↥X ≤ p := by
      have := hmin.minimal (zpowers a) ((hY₁R.trans hR₁Q)) hY₁0 hY₁z hY₁N
      rwa [hcardY₁] at this
    have hXcard : Nat.card ↥X = p := le_antisymm hle1 (prime_le_card_of_ne_bot hp hXp hmin.X_ne)
    have hXnc : ¬ X ≤ Cen z := by
      refine hmin.prefer ⟨zpowers a, (hY₁R.trans hR₁Q), hY₁0, hY₁z, hY₁N, by rw [hcardY₁, hXcard], ?_⟩
      intro hle
      have hac : a ∈ Cen z := hle (Subgroup.mem_zpowers a)
      have hcomm : a * z = z * a := Subgroup.mem_centralizer_singleton_iff.mp hac
      apply ne_inv_of_prime hp hp2 ha1 hap
      calc a = z * a * z⁻¹ := by rw [← hcomm]; group
        _ = a⁻¹ := hainv
    obtain ⟨a', ha'X, ha'1, ha'inv⟩ := exists_inverted hz2 hmin.X_inv hXnc
    have hap' : a' ^ p = 1 := hexp a' (hXQ ha'X)
    have hcard' : Nat.card ↥(zpowers a') = p := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime hap' ha'1
    have hXeq : zpowers a' = X :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha'X) (by rw [hcard', hXcard])
    refine ⟨hXcard, ?_⟩
    rw [← hXeq]
    exact inverts_zpowers ha'inv
  ·
    intro hab
    have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    exact hcc (le_normalizer_of_commutes fun x hx y hy => hcomm x (hRQ hx) y (hR₁Q hy))
  ·
    intro v hvZ hv1
    by_contra hnot
    have hvQ : v ∈ Q := hZQ hvZ
    have hvc : v ∈ centralizer (Q : Set G) := hZc hvZ
    have hvz : z * v = v * z := (Subgroup.mem_centralizer_singleton_iff.mp (he hvZ)).symm
    have hzv : z ∈ normalizer ((zpowers v : Subgroup G) : Set G) := mem_normalizer_zpowers_of_comm hvz
    have hv0 : zpowers v ≠ ⊥ := by
      intro h
      apply hv1
      have : v ∈ zpowers v := Subgroup.mem_zpowers v
      rw [h] at this
      exact Subgroup.mem_bot.mp this
    have hQcv : Q ≤ centralizer ((zpowers v : Subgroup G) : Set G) := by
      intro q hq
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hc : Commute q v := Subgroup.mem_centralizer_iff.mp hvc q hq
      exact (hc.symm.zpow_left n).eq
    have hRn : ⁅Q, zpowers z⁆ ≤ normalizer ((zpowers v : Subgroup G) : Set G) :=
      hRQ.trans (hQcv.trans (Subgroup.centralizer_le_normalizer _))
    exact h610 G z k S M p hC (zpowers v) ⁅Q, zpowers z⁆
      (Subgroup.zpowers_le.mpr (hQP hvQ)) hv0 hzv hnot (le_inf (hRQ.trans hQP) hRn) hR0 hRc hRN

end L611

end CFSG.GH74.GLS.Stage2.Bender.Thm1
