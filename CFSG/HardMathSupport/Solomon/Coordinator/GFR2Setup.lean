module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2Layer
public import CFSG.HardMathSupport.Solomon.Coordinator.GapFinalSetup

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

variable {G : Type} [Group G] [Finite G]

theorem gfr2_le_conjHull {a : G} {J : Subgroup G} : J ≤ conjHull a J := by
  have := le_iSup₂ (f := fun g (_ : g ∈ GLAPLayer 3 (Cen a)) => GLBConj g J) 1 (one_mem _)
  rwa [gLBConj_one] at this

theorem gfr2_nonempty_equiv_barX {X J : Subgroup G} (hJX : J ≤ X) :
    Nonempty (barOf 3 J ≃* barOf 3 (barX 3 X J)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  set ψ₀ : ↥X →* ↥X ⧸ GLAPPrimeCore 3 ↥X := QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) with hψ₀
  have hker1 : ∀ S : Subgroup ↥X, Nat.Coprime 3 (Nat.card ↥(S ⊓ ψ₀.ker)) := by
    intro S
    have hkr : ψ₀.ker = GLAPPrimeCore 3 ↥X := QuotientGroup.ker_mk' _
    have h1 : Nat.card ↥(S ⊓ ψ₀.ker) ∣ Nat.card ↥(GLAPPrimeCore 3 ↥X) := by
      rw [hkr]
      exact Subgroup.card_dvd_of_le inf_le_right
    exact Nat.Coprime.coprime_dvd_right h1 (coprime_card_gLAPPrimeCore_aux 3 ↥X)
  have hker2 : ∀ S : Subgroup ↥X, Nat.Coprime 3 (Nat.card ↥(S ⊓ X.subtype.ker)) := by
    intro S
    rw [X.ker_subtype, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  set K₀ : Subgroup ↥X := J.subgroupOf X with hK₀
  have hJeq : K₀.map X.subtype = J := by
    rw [hK₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hJX]
  have key : ∀ J₂ : Subgroup G, K₀.map X.subtype = J₂ →
      Nonempty (barOf 3 J₂ ≃* barOf 3 (K₀.map ψ₀)) := by
    rintro _ rfl
    exact ⟨(lcEquiv hp X.subtype K₀ (hker2 K₀)).symm.trans (lcEquiv hp ψ₀ K₀ (hker1 K₀))⟩
  exact key J hJeq

theorem gfr2_data (h183 : Lemma512Ns.Input18_3) [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) (hkp : CFSG.Open.IsKProper G) {a b : G}
    (hbo : orderOf b = 3) (hao : orderOf a = 3) (hab : b * a = a * b)
    {L J : Subgroup G} (hL : GLAPComponent 3 (Cen b) L)
    (hJ : GLAPComponent 3 (L ⊓ Cen a) J) (hty : IsHatON (barOf 3 J) ∨ IsHatSix (barOf 3 J))
    (hbJ : b ∈ J) (hK : GLAPComponent 3 (Cen a) (conjHull a J))
    (hbK : b ∈ conjHull a J) :
    ∃ J₁ : Subgroup (barOf 3 (conjHull a J)),
      GLAPComponent 3 (Subgroup.centralizer
        ({(QuotientGroup.mk' (GLAPPrimeCore 3 ↥(conjHull a J)) ⟨b, hbK⟩ : barOf 3 (conjHull a J))} :
          Set (barOf 3 (conjHull a J)))) J₁ ∧
      (IsHatON (barOf 3 J₁) ∨ IsHatSix (barOf 3 J₁)) ∧
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(conjHull a J)) ⟨b, hbK⟩ : barOf 3 (conjHull a J)) ∈ J₁ := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hLle : L ≤ GLAPLayer 3 (Cen b) := le_sSup hL
  have hLayer_le : ∀ X : Subgroup G, GLAPLayer 3 X ≤ X := fun X => sSup_le fun K hK => hK.1
  have hLsn : CFSG.Open.IsSubnormal L (GLAPLayer 3 (Cen b)) :=
    isSubnormal_of_le_of_le hL.2.1 hLle (hLayer_le _)
  have hHsnM : CFSG.Open.IsSubnormal (L ⊓ Cen a) (GLAPLayer 3 (Cen b) ⊓ Cen a) :=
    isSubnormal_inf hLsn (Cen a)
  have hJsnM : CFSG.Open.IsSubnormal J (GLAPLayer 3 (Cen b) ⊓ Cen a) :=
    isSubnormal_trans' hJ.2.1 hHsnM
  have hJM : GLAPComponent 3 (GLAPLayer 3 (Cen b) ⊓ Cen a) J :=
    glaPComponent_up hp hJ (inf_le_inf_right _ hLle) hJsnM
  have hJMle : J ≤ GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen a) := le_sSup hJM
  have hJMl : GLAPComponent 3 (GLAPLayer 3 (GLAPLayer 3 (Cen b) ⊓ Cen a)) J :=
    glaPComponent_down hp hJM hJMle (hLayer_le _)
  obtain ⟨-, h3⟩ := h183 G hnab hkp b a hbo hao hab J hJMl
  have hbC : b ∈ Cen a := Subgroup.mem_centralizer_singleton_iff.2 hab
  have h3' := h3 hbC
  set K : Subgroup G := conjHull a J with hKdef
  have hKsn : CFSG.Open.IsSubnormal K (Cen a) := hK.2.1
  have hKC : K ≤ Cen a := CFSG.LocalAnalysis.GLTheoremB.isSubnormal_le' hKsn
  set K' : Subgroup (CBarOf a) := barX 3 (Cen a) K with hK'
  let ψ : ↥K →* CBarOf a :=
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen a))).comp (Subgroup.inclusion hKC)
  have hψker : ∀ k : ↥K, ψ k = 1 ↔ k ∈ GLAPPrimeCore 3 ↥K := by
    intro k
    show (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cen a))) (Subgroup.inclusion hKC k) = 1 ↔ _
    refine (QuotientGroup.eq_one_iff (N := GLAPPrimeCore 3 ↥(Cen a)) _).trans ?_
    have h1 : (k : G) ∈ GLAPPrimeCoreOf 3 K ↔ k ∈ GLAPPrimeCore 3 ↥K := by
      rw [mem_gLAPPrimeCoreOf_iff]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩
    have h2 : (k : G) ∈ GLAPPrimeCoreOf 3 (Cen a) ↔
        Subgroup.inclusion hKC k ∈ GLAPPrimeCore 3 ↥(Cen a) := by
      rw [mem_gLAPPrimeCoreOf_iff]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hKC k.2, h⟩⟩
    have h3 : (k : G) ∈ GLAPPrimeCoreOf 3 K ↔ (k : G) ∈ GLAPPrimeCoreOf 3 (Cen a) := by
      rw [← inf_gLAPPrimeCoreOf_eq hp hKsn]
      exact ⟨fun h => (Subgroup.mem_inf.1 h).2, fun h => Subgroup.mem_inf.2 ⟨k.2, h⟩⟩
    rw [← h2, ← h3, h1]
  let Φ : barOf 3 K →* CBarOf a :=
    QuotientGroup.lift (GLAPPrimeCore 3 ↥K) ψ (fun k hk => (hψker k).2 hk)
  have hΦmk : ∀ k : ↥K, Φ (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) k) = ψ k := fun k => rfl
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) q
    rw [hΦmk] at hq
    exact (QuotientGroup.eq_one_iff _).2 ((hψker k).1 hq)
  have hΦmem : ∀ y, Φ y ∈ K' := by
    intro y
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥K) y
    rw [hΦmk]
    exact ⟨⟨k, hKC k.2⟩, Subgroup.mem_subgroupOf.2 k.2, rfl⟩
  have hΦsurj : ∀ z ∈ K', ∃ y, Φ y = z := by
    rintro z ⟨⟨k, hk⟩, hkK, rfl⟩
    exact ⟨QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨k, Subgroup.mem_subgroupOf.1 hkK⟩, rfl⟩
  set yb : barOf 3 K := QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) ⟨b, hbK⟩ with hyb
  set ub : CBarOf a := QuotientGroup.mk ⟨b, hbC⟩ with hub
  have hΦyb : Φ yb = ub := rfl
  set H : Subgroup (CBarOf a) := K' ⊓ Subgroup.centralizer ({ub} : Set (CBarOf a)) with hH
  set A : Subgroup (barOf 3 K) := Subgroup.centralizer ({yb} : Set (barOf 3 K)) with hA
  have hAmap : A.map Φ = H := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hΦmem y, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hy
      rw [← hΦyb, ← map_mul, ← map_mul, this]
    · rintro ⟨hzK, hzc⟩
      obtain ⟨y, rfl⟩ := hΦsurj z hzK
      refine ⟨y, Subgroup.mem_centralizer_singleton_iff.2 (hΦinj ?_), rfl⟩
      rw [map_mul, map_mul, hΦyb]
      exact Subgroup.mem_centralizer_singleton_iff.1 hzc
  set J' : Subgroup (CBarOf a) := barX 3 (Cen a) J with hJ'
  have hJ'comp : IsComponentOf J' (GLALayer H) := h3'
  have hJle : J ≤ Cen a := (hJ.1).trans inf_le_right
  obtain ⟨e⟩ := gfr2_nonempty_equiv_barX hJle
  have hqJ : CFSG.Open.IsQuasisimple (barOf 3 J) :=
    (isQuasisimple_barX_iff hp hJ.2.1).1 hJ.2.2.1.2.2
  have hqJ' : CFSG.Open.IsQuasisimple (barOf 3 J') :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e hqJ
  have hJ'H : GLAPComponent 3 H J' := gfr2_glaPComponent_of_layer hJ'comp hqJ'
  have hker : ∀ S : Subgroup (barOf 3 K), Nat.Coprime 3 (Nat.card ↥(S ⊓ Φ.ker)) := by
    intro S
    rw [(MonoidHom.ker_eq_bot_iff Φ).2 hΦinj, inf_bot_eq, Subgroup.card_bot]
    exact Nat.coprime_one_right 3
  obtain ⟨J₁, hJ₁, hJ₁map⟩ := exists_glaPComponent_map_eq hp Φ (A := A) (hker A)
    (K' := J') (by rw [hAmap]; exact hJ'H)
  have hubJ' : ub ∈ J' := ⟨⟨b, hbC⟩, Subgroup.mem_subgroupOf.2 hbJ, rfl⟩
  have hybJ₁ : yb ∈ J₁ := by
    rw [← hJ₁map] at hubJ'
    obtain ⟨y, hy, hyyb⟩ := hubJ'
    rw [← hΦyb] at hyyb
    rw [← hΦinj hyyb]
    exact hy
  have key : ∀ J₂ : Subgroup (CBarOf a), J₁.map Φ = J₂ →
      Nonempty (barOf 3 J₁ ≃* barOf 3 J₂) := by
    rintro _ rfl
    exact ⟨lcEquiv hp Φ J₁ (hker J₁)⟩
  obtain ⟨e₂⟩ := key J' hJ₁map
  refine ⟨J₁, hJ₁, ?_, hybJ₁⟩
  exact isHatON_or_isHatSix_of_mulEquiv (e.trans e₂.symm) hty

end CFSG.HardMathSupport.Solomon.Coordinator
