module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerBasic
public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] noncomputable def te6Inv (p f : ℕ) [Fact p.Prime] :
    Su (GaloisField p (2 * f)) p f (5 + 1) :=
  zEltU (GaloisField p (2 * f)) p f (nodePair 5 0 (by norm_num))

abbrev TE6Layer (p f : ℕ) [Fact p.Prime] : Type :=
  Option {R : Subgroup (Su (GaloisField p (2 * f)) p f (5 + 1)) //
    R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 5 + 1) ∧
      R ≤ Subgroup.centralizer ({te6Inv p f} : Set _)}

@[expose] def TE6Layer.rel : TE6Layer p f → TE6Layer p f → Prop
  | none, none => False
  | none, some _ => True
  | some _, none => True
  | some R, some R' => Commutes R.1 R'.1

@[expose] def TE6PerpTable (p f : ℕ) [Fact p.Prime] : Prop :=
  PerpTable p (TE6Layer.rel (p := p) (f := f)) .POmegaMinus 5

section Visible

variable [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem UNodes.psi_inv {m : ℕ} (c : UCtx p f m Ω K z) (nd : UNodes c) {a : ℕ} (ha : a < m) :
    c.d.ψ (zEltU (GaloisField p (2 * f)) p f (nodePair m a ha)) =
      locElt Ω z (nd.w a) (le_centralizingLayer (nd.mem a ha) (nd.isCl a ha).mem) :=
  psiU_root_inv c.hp2 c.hq c.hm c.d (isLongRootSU2_LcU c.h2 c.hn _) (nd.img a ha)
    (le_centralizingLayer (nd.mem a ha)) (nd.isCl a ha).mem (nd.isCl a ha).orderOf_eq_two

theorem UNodes.le_centralizer_iff_root_node {m : ℕ} (c : UCtx p f m Ω K z) (nd : UNodes c)
    {a : ℕ} (ha : a < m) {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z})
    {ρ : Subgroup (Su (GaloisField p (2 * f)) p f (m + 1))}
    (hρ : ρ ≤ ⁅ρ, ρ⁆) (hNρ : locImg Ω z N = ρ.map c.d.ψ) :
    N ≤ Subgroup.centralizer ({nd.w a} : Set G) ↔
      ρ ≤ Subgroup.centralizer
        ({zEltU (GaloisField p (2 * f)) p f (nodePair m a ha)} : Set _) := by
  have hw : nd.w a ∈ locLayer Ω z :=
    le_centralizingLayer (nd.mem a ha) (nd.isCl a ha).mem
  have h1 := le_centralizer_iff_locImg c.hΩ c.hP1 hN ⟨nd.w a, hw⟩
  have h2 := le_centralizer_iff_map c.d.ψ c.d.ker_le hρ
    (zEltU (GaloisField p (2 * f)) p f (nodePair m a ha))
  have h3 : c.d.ψ (zEltU (GaloisField p (2 * f)) p f (nodePair m a ha)) =
      locElt Ω z (nd.w a) hw := UNodes.psi_inv c nd ha
  rw [h2, h3, ← hNρ]
  exact h1

theorem UNodes.le_centralizer_iff_root (c : UCtx p f 5 Ω K z) (nd : UNodes c)
    {N : Subgroup G} (hN : N ∈ centralizingMembers Ω {z})
    {ρ : Subgroup (Su (GaloisField p (2 * f)) p f (5 + 1))}
    (hρ : ρ ≤ ⁅ρ, ρ⁆) (hNρ : locImg Ω z N = ρ.map c.d.ψ) :
    N ≤ Subgroup.centralizer ({nd.w 0} : Set G) ↔
      ρ ≤ Subgroup.centralizer ({te6Inv p f} : Set _) :=
  UNodes.le_centralizer_iff_root_node c nd (by norm_num : 0 < 5) hN hρ hNρ

theorem exists_visible_equiv (c : UCtx p f 5 Ω K z) (nd : UNodes c) :
    ∃ φ : {N : Subgroup G // N ∈ centralizingMembers Ω {z * nd.w 0, z}} ≃ TE6Layer p f,
      ∀ N N', Commutes N.1 N'.1 ↔ TE6Layer.rel (φ N) (φ N') := by
  classical
  have hKz : K ∈ centralizingMembers Ω {z} := ⟨c.hK, le_centralizer_of_isClassicalMember c.hz⟩
  have hKvis : K ∈ centralizingMembers Ω {z * nd.w 0, z} := by
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hKz, le_centralizer_of_commutes (nd.commK 0 (by norm_num))
      (nd.isCl 0 (by norm_num)).mem⟩
  have hperf : ∀ ρ ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) c.hn,
      ρ ≤ ⁅ρ, ρ⁆ := by
    rintro ρ ⟨i, hi⟩
    exact (Subgroup.isPerfect_iff.mp (c.isPerfect_of_isLongRootSU2 hi)).ge
  have hmem : ∀ ρ : {R : Subgroup (Su (GaloisField p (2 * f)) p f (5 + 1)) //
      R ∈ longRootSetU (K := GaloisField p (2 * f)) (p := p) (f := f) (by norm_num : 2 ≤ 5 + 1) ∧
        R ≤ Subgroup.centralizer ({te6Inv p f} : Set _)},
      ∃ L ∈ centralizingMembers Ω {z}, L ≠ K ∧ locImg Ω z L = ρ.1.map c.d.ψ :=
    fun ρ => typeU_exists_member_of_root c.hp2 c.hq c.hm c.hΩ c.hK c.hz c.hP1 c.d ρ.2.1
  choose Lof hLz hLK hLimg using hmem
  have hvis : ∀ ρ, Lof ρ ∈ centralizingMembers Ω {z * nd.w 0, z} := by
    intro ρ
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair]
    exact ⟨hLz ρ, (UNodes.le_centralizer_iff_root c nd (hLz ρ) (hperf _ ρ.2.1) (hLimg ρ)).mpr
      ρ.2.2⟩
  let ι : TE6Layer p f → {N : Subgroup G // N ∈ centralizingMembers Ω {z * nd.w 0, z}} :=
    fun a => Option.elim a ⟨K, hKvis⟩ fun ρ => ⟨Lof ρ, hvis ρ⟩
  have hinj : Function.Injective ι := by
    intro a b hab
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · rfl
    · exact absurd (congrArg Subtype.val hab).symm (hLK ρ')
    · exact absurd (congrArg Subtype.val hab) (hLK ρ)
    · have h : Lof ρ = Lof ρ' := congrArg Subtype.val hab
      have himg : ρ.1.map c.d.ψ = ρ'.1.map c.d.ψ := by
        rw [← hLimg ρ, ← hLimg ρ', h]
      exact congrArg some (Subtype.ext (eq_of_map_eq_of_central c.d.ψ c.d.ker_le
        (hperf _ ρ.2.1) (hperf _ ρ'.2.1) himg))
  have hsurj : Function.Surjective ι := by
    rintro ⟨N, hN⟩
    rw [centralizingMembers_mul_iff, mem_centralizingMembers_pair] at hN
    obtain ⟨hNz, hNw⟩ := hN
    by_cases hNK : N = K
    · exact ⟨none, Subtype.ext hNK.symm⟩
    · obtain ⟨ρ, hρT, hNρ⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1
        c.d hNz hNK
      have hρc : ρ ≤ Subgroup.centralizer ({te6Inv p f} : Set _) :=
        (UNodes.le_centralizer_iff_root c nd hNz (hperf ρ hρT) hNρ).mp hNw
      refine ⟨some ⟨ρ, hρT, hρc⟩, Subtype.ext ?_⟩
      exact locImg_injOn c.hΩ c.hP1 (hLz _) hNz ((hLimg ⟨ρ, hρT, hρc⟩).trans hNρ.symm)
  have key : ∀ a b : TE6Layer p f, Commutes (ι a).1 (ι b).1 ↔ TE6Layer.rel a b := by
    intro a b
    rcases a with _ | ρ <;> rcases b with _ | ρ'
    · exact iff_false_intro (not_commutes_self_of_isClassicalMember c.hz)
    · exact iff_true_intro (typeU_commutes_K_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d
        (hLz ρ') (hLK ρ'))
    · exact iff_true_intro (commutes_symm (typeU_commutes_K_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK
        c.hz c.hP1 c.d (hLz ρ) (hLK ρ)))
    · obtain ⟨i, hi⟩ := ρ.2.1
      exact c.commutes_iff_root (hLz ρ) (hLz ρ') hi (hLimg ρ) (hLimg ρ')
  refine ⟨(Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm, fun N N' => ?_⟩
  have h1 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N) = N :=
    (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N
  have h2 : ι ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N') = N' :=
    (Equiv.ofBijective ι ⟨hinj, hsurj⟩).apply_symm_apply N'
  have := key ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N)
    ((Equiv.ofBijective ι ⟨hinj, hsurj⟩).symm N')
  rwa [h1, h2] at this

end Visible

end CFSG.ClassicalInvolution.RouteD.NonClassical
