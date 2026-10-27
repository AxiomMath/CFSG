module

public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR17
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR4
public import CFSG.GH74.GLS.C3.Layer1.Th2P78Fixed

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
open scoped commutatorElement

section A7Glue

variable {G : Type} [Group G] [Finite G]

theorem exists_cbar_A7_in_D {x t : G} {K J B D : Subgroup G} (hlt : PumpUpLT 2 x K t J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K)
    (eA : kBar K ≃* alternatingGroup (Fin 7))
    (hBJ : B ≤ normalizer (J : Set G)) (hBel : CFSG.IsElementaryAbelian 2 ↥B) (htB : t ∈ B)
    (hDB : D ≤ B) (hDK : D ≤ K) (hDel : CFSG.IsElementaryAbelian 2 ↥D) (hD4 : Nat.card D = 4)
    (hD6 : Set.ncard {i : Fin 7 | ∃ d ∈ D, ∃ hd : d ∈ K,
      ((eA (QuotientGroup.mk (⟨d, hd⟩ : ↥K)) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) i ≠ i} = 6) :
    ∃ (V : Subgroup G) (hVB : V ≤ B) (b : G) (hbB : b ∈ B) (hbD : b ∈ D),
      Nat.card B = 2 * Nat.card V ∧
      ∃ c : kBar J, Nat.Prime (orderOf c) ∧ Odd (orderOf c) ∧
        (∀ v (hv : v ∈ V), barAct J ⟨v, hBJ (hVB hv)⟩ c = c) ∧
        barAct J ⟨b, hBJ hbB⟩ c = c⁻¹ ∧
        c ∈ pPrimeCoreOf 2 (CFSG.GH74.GLS.Th2.Fixed.kBarFixedBy J V (hVB.trans hBJ)) ∧
        (∀ g (hg : g ∈ B), barAct J ⟨g, hBJ hg⟩ = 1 → g ∈ V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Θ, hΘ⟩ := exists_theta hlt hxJ e
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hBel
  obtain ⟨hDc, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  let Φ : kBar J ≃* alternatingGroup (Fin 7) := Θ.trans eA
  have hbij : Function.Bijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)) :
      Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7))) :=
    CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by norm_num) (by norm_num)
  let cN : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7))) hbij
  let α' : ↥B →* MulAut (alternatingGroup (Fin 7)) :=
    (MulAut.congr Φ).toMonoidHom.comp ((barAct J).comp (Subgroup.inclusion hBJ))
  let θ : ↥B →* Equiv.Perm (Fin 7) := cN.symm.toMonoidHom.comp α'
  have hθα : ∀ g : ↥B, MulAut.conjNormal (θ g) = α' g := fun g => cN.apply_symm_apply (α' g)
  have hθD : ∀ (d : G) (hdB : d ∈ B) (hdK : d ∈ K),
      θ ⟨d, hdB⟩ = ((eA (QuotientGroup.mk (⟨d, hdK⟩ : ↥K)) : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) := by
    intro d hdB hdK
    apply hbij.1
    rw [hθα]
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    have htd : d * t = t * d := hBc d hdB t htB
    have h1 : Θ (barAct J ⟨d, hBJ hdB⟩ (Φ.symm a)) =
        QuotientGroup.mk ⟨d, hdK⟩ * Θ (Φ.symm a) * (QuotientGroup.mk ⟨d, hdK⟩)⁻¹ := by
      rw [hΘ d (hBJ hdB) (Subgroup.le_normalizer hdK) htd]
      have := barAct_of_mem hdK
      rw [this]
      rfl
    have h2 : eA (Θ (Φ.symm a)) = a := by
      have := Φ.apply_symm_apply a
      exact this
    have h3 : α' ⟨d, hdB⟩ a = eA (QuotientGroup.mk ⟨d, hdK⟩) * a * (eA (QuotientGroup.mk ⟨d, hdK⟩))⁻¹ := by
      change eA (Θ (barAct J ⟨d, hBJ hdB⟩ (Φ.symm a))) = _
      rw [h1, map_mul, map_mul, map_inv, h2]
    rw [h3, MulAut.conjNormal_apply]
    simp
  have hact : ∀ (g : ↥B) (a : alternatingGroup (Fin 7)),
      ((α' g a : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) = θ g * a * (θ g)⁻¹ := by
    intro g a
    rw [← hθα g, MulAut.conjNormal_apply]
  have hΦ : ∀ (g : ↥B) (a : alternatingGroup (Fin 7)),
      α' g a = Φ (barAct J ⟨(g : G), hBJ g.2⟩ (Φ.symm a)) := fun g a => rfl
  let DB : Subgroup ↥B := D.subgroupOf B
  have hDBcard : Nat.card DB = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv
  have hθDinj : Function.Injective (θ.comp DB.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyD : (y.1 : G) ∈ D := Subgroup.mem_subgroupOf.1 y.2
    have hyK := hDK hyD
    have h1 : θ y.1 = 1 := hy
    have h1' : θ ⟨(y.1 : G), y.1.2⟩ = 1 := h1
    rw [hθD (y.1 : G) y.1.2 hyK] at h1'
    have h2 : eA (QuotientGroup.mk ⟨(y.1 : G), hyK⟩) = 1 := Subtype.ext h1'
    have h3 : (QuotientGroup.mk ⟨(y.1 : G), hyK⟩ : kBar K) = 1 := by
      have := congrArg eA.symm h2
      simpa using this
    have hO : (⟨(y.1 : G), hyK⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
    have hsq : (⟨(y.1 : G), hyK⟩ : ↥K) * ⟨(y.1 : G), hyK⟩ = 1 := Subtype.ext (hDsq _ hyD)
    have := congrArg Subtype.val (Th2.Bal.eq_one_of_sq_of_mem_pPrimeCore hsq hO)
    exact Subtype.ext (Subtype.ext this)
  let Dp : Subgroup (Equiv.Perm (Fin 7)) := (θ.comp DB.subtype).range
  have hDpcard : Nat.card Dp = 4 := by
    rw [← hD4, ← hDBcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hθDinj).toEquiv).symm
  have hDpA : Dp ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨y, rfl⟩
    have hyD : (y.1 : G) ∈ D := Subgroup.mem_subgroupOf.1 y.2
    show θ y.1 ∈ _
    have : θ y.1 = ((eA (QuotientGroup.mk ⟨(y.1 : G), hDK hyD⟩) : alternatingGroup (Fin 7)) :
        Equiv.Perm (Fin 7)) := hθD (y.1 : G) y.1.2 (hDK hyD)
    rw [this]
    exact (eA _).2
  have hDpR : Dp ≤ θ.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨y.1, rfl⟩
  have hcomm : ∀ a ∈ θ.range, ∀ b ∈ θ.range, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc a a.2 b b.2)
  have hsq : ∀ a ∈ θ.range, a * a = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hBsq a a.2)
    rw [this, map_one]
  have hRg4 : Nat.card ↥(θ.range ⊓ alternatingGroup (Fin 7)) ≤ 4 := by
    let A' : Subgroup ↥(alternatingGroup (Fin 7)) :=
      (θ.range ⊓ alternatingGroup (Fin 7)).subgroupOf (alternatingGroup (Fin 7))
    have h1 : Nat.card A' ≤ 4 :=
      IVK.card_le_four_of_dihedralSylow CFSG.GorensteinWalter.hasDihedralSylowTwo_alternatingGroupSeven
        A' (fun x hx y hy => Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.1 hx).1 _
          (Subgroup.mem_subgroupOf.1 hy).1))
        (fun x hx => Subtype.ext (hsq _ (Subgroup.mem_subgroupOf.1 hx).1))
    have h2 : Nat.card A' = Nat.card ↥(θ.range ⊓ alternatingGroup (Fin 7)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    omega
  have hDpeq : Dp = θ.range ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge (le_inf hDpR hDpA) (by rw [hDpcard]; exact hRg4)
  have hRg4' : Nat.card ↥(θ.range ⊓ alternatingGroup (Fin 7)) = 4 := by
    rw [← hDpeq]; exact hDpcard
  have hsix : Set.ncard {i : Fin 7 | ∃ d ∈ θ.range ⊓ alternatingGroup (Fin 7), d i ≠ i} = 6 := by
    have hset : {i : Fin 7 | ∃ d ∈ θ.range ⊓ alternatingGroup (Fin 7), d i ≠ i} =
        {i : Fin 7 | ∃ d ∈ D, ∃ hd : d ∈ K, ((eA (QuotientGroup.mk (⟨d, hd⟩ : ↥K)) :
          alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) i ≠ i} := by
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨d', hd', hne⟩
        have hd'Dp : d' ∈ Dp := by rw [hDpeq]; exact hd'
        obtain ⟨y, rfl⟩ := hd'Dp
        have hyD : (y.1 : G) ∈ D := Subgroup.mem_subgroupOf.1 y.2
        refine ⟨(y.1 : G), hyD, hDK hyD, ?_⟩
        have h1 : θ y.1 = ((eA (QuotientGroup.mk ⟨(y.1 : G), hDK hyD⟩) : alternatingGroup (Fin 7)) :
            Equiv.Perm (Fin 7)) := hθD (y.1 : G) y.1.2 (hDK hyD)
        have h2 : (θ.comp DB.subtype) y = θ y.1 := rfl
        rw [h2, h1] at hne
        exact hne
      · rintro ⟨d, hdD, hdK, hne⟩
        have hdB : d ∈ B := hDB hdD
        have h1 : θ ⟨d, hdB⟩ = ((eA (QuotientGroup.mk ⟨d, hdK⟩) : alternatingGroup (Fin 7)) :
            Equiv.Perm (Fin 7)) := hθD d hdB hdK
        refine ⟨θ ⟨d, hdB⟩, ⟨⟨⟨d, hdB⟩, rfl⟩, ?_⟩, ?_⟩
        · rw [h1]; exact (eA _).2
        · rw [h1]; exact hne
    rw [hset]; exact hD6
  have hel : CFSG.IsElementaryAbelian 2 ↥θ.range := isElementaryAbelian_two_of_comm_sq hcomm hsq
  obtain ⟨V', hV'le, b', hb'mem, hcardV', c', hc'3, hc'mem, hc'inv⟩ :=
    IVK.ivk_10_6_A7 (H := ⊤) (B := θ.range) le_top hel hRg4' hsix
  obtain ⟨V, hVB, hVcard, hVmem, hVback⟩ := exists_pullback θ hV'le hcardV'
  have hb'Dp : b' ∈ Dp := by rw [hDpeq]; exact hb'mem
  obtain ⟨bb, hbb⟩ : b' ∈ Dp := hb'Dp
  let bbB : ↥B := bb.1
  have hbbB : θ bbB = b' := by simpa [bbB] using hbb
  have hbD : (bbB : G) ∈ D := Subgroup.mem_subgroupOf.1 bb.2
  have hc'A : c' ∈ alternatingGroup (Fin 7) :=
    mem_alternatingGroup_of_odd_orderOf (by rw [hc'3]; decide)
  have hc'cent : ∀ w ∈ V', w * c' = c' * w := fun w hw =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (TwoThin.pPrimeCoreOf_le _ hc'mem)).1 w hw
  have hcord : orderOf (Φ.symm (⟨c', hc'A⟩ : alternatingGroup (Fin 7))) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hc'3
  have hrel : ∀ (b : ↥B) (x : kBar J),
      ((Φ (barAct J ⟨b, hBJ b.2⟩ x) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) =
        θ b * ((Φ x : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * (θ b)⁻¹ := by
    intro b x
    have h1 := hact b (Φ x)
    have h2 : α' b (Φ x) = Φ (barAct J ⟨b, hBJ b.2⟩ x) := by
      rw [hΦ b (Φ x), Φ.symm_apply_apply]
    rw [← h2]
    exact h1
  have hθV_eq : (V' : Set (Equiv.Perm (Fin 7))) =
      Set.range (θ.comp (Subgroup.inclusion hVB)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨b, hb⟩ := hV'le hy
      have hbV : (b : G) ∈ V := hVback b (by rwa [← hb] at hy)
      refine ⟨⟨(b : G), hbV⟩, ?_⟩
      simpa [Subgroup.inclusion] using hb
    · rintro ⟨v, rfl⟩
      exact hVmem v.1 v.2
  have hc'core : c' ∈ pPrimeCoreOf 2
      (Subgroup.centralizer (Set.range (θ.comp (Subgroup.inclusion hVB)) :
        Set (Equiv.Perm (Fin 7)))) := by
    have htmp : c' ∈ pPrimeCoreOf 2
        (Subgroup.centralizer (V' : Set (Equiv.Perm (Fin 7)))) := by
      simpa using hc'mem
    rwa [hθV_eq] at htmp
  have hcore : Φ.symm ⟨c', hc'A⟩ ∈ pPrimeCoreOf 2
      (CFSG.GH74.GLS.Th2.Fixed.kBarFixedBy J V (hVB.trans hBJ)) :=
    CFSG.GH74.GLS.Th2.Fixed.kBarFixedBy_oddCore_of_A7 hBJ hVB Φ θ hrel hc'A hc'core (by simp)
  have hker : ∀ g (hg : g ∈ B), barAct J ⟨g, hBJ hg⟩ = 1 → g ∈ V := by
    intro g hg hbar
    have hα : α' ⟨g, hg⟩ = 1 := by
      change MulAut.congr Φ (barAct J ⟨g, hBJ hg⟩) = 1
      rw [hbar, map_one]
    have hθ : θ ⟨g, hg⟩ = 1 := by
      change cN.symm (α' ⟨g, hg⟩) = 1
      rw [hα, map_one]
    exact hVback ⟨g, hg⟩ (by rw [hθ]; exact V'.one_mem)
  refine ⟨V, hVB, (bbB : G), bbB.2, hbD, hVcard, Φ.symm ⟨c', hc'A⟩, ?_, ?_, ?_, ?_, hcore, hker⟩
  · rw [hcord]; exact Nat.prime_three
  · rw [hcord]; decide
  · intro v hv
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply]
    have h1 := hΦ ⟨v, hVB hv⟩ ⟨c', hc'A⟩
    rw [← h1]
    apply Subtype.ext
    rw [hact]
    have h2 := hc'cent _ (hVmem v hv)
    show θ ⟨v, hVB hv⟩ * c' * (θ ⟨v, hVB hv⟩)⁻¹ = c'
    rw [h2]; group
  · apply Φ.injective
    rw [map_inv, MulEquiv.apply_symm_apply]
    have h1 := hΦ bbB ⟨c', hc'A⟩
    rw [← h1]
    apply Subtype.ext
    rw [hact]
    show θ bbB * c' * (θ bbB)⁻¹ = c'⁻¹
    rw [hbbB]
    exact hc'inv

theorem exists_cbar_A7 {x t : G} {K J B D : Subgroup G} (hlt : PumpUpLT 2 x K t J)
    (hxJ : x ∈ normalizer (J : Set G)) (e : kBar J ≃* kBar K)
    (eA : kBar K ≃* alternatingGroup (Fin 7))
    (hBJ : B ≤ normalizer (J : Set G)) (hBel : CFSG.IsElementaryAbelian 2 ↥B) (htB : t ∈ B)
    (hDB : D ≤ B) (hDK : D ≤ K) (hDel : CFSG.IsElementaryAbelian 2 ↥D) (hD4 : Nat.card D = 4)
    (hD6 : Set.ncard {i : Fin 7 | ∃ d ∈ D, ∃ hd : d ∈ K,
      ((eA (QuotientGroup.mk (⟨d, hd⟩ : ↥K)) : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) i ≠ i} = 6) :
    ∃ (V : Subgroup G) (hVB : V ≤ B) (b : G) (hbB : b ∈ B), Nat.card B = 2 * Nat.card V ∧
      ∃ c : kBar J, Nat.Prime (orderOf c) ∧ Odd (orderOf c) ∧
        (∀ v (hv : v ∈ V), barAct J ⟨v, hBJ (hVB hv)⟩ c = c) ∧
        barAct J ⟨b, hBJ hbB⟩ c = c⁻¹ := by
  obtain ⟨V, hVB, b, hbB, -, hVcard, c, hc, hodd, hfix, hinv, -, -⟩ :=
    exists_cbar_A7_in_D hlt hxJ e eA hBJ hBel htB hDB hDK hDel hD4 hD6
  exact ⟨V, hVB, b, hbB, hVcard, c, hc, hodd, hfix, hinv⟩

end A7Glue

end CFSG.GH74.GLS.Th2.Obs
