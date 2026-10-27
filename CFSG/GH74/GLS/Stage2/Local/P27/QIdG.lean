module

public import CFSG.GH74.GLS.Stage2.Local.P27.QIdMain
public import CFSG.GH74.GLS.Stage2.Local.P27.QIdLift
public import CFSG.GH74.GLS.Stage2.Local.P34S5Clo
public import CFSG.GH74.GLS.Stage2.Local.P34S5Frat

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27.QId

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P34

section Action

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def cAut (x c : G) (hc : c ∈ centralizer ({x} : Set G)) :
    MulAut ↥(Jx x) where
  toFun g := ⟨c * g * c⁻¹, Jx_normalized x c hc g g.2⟩
  invFun g := ⟨c⁻¹ * g * c, by simpa using Jx_normalized x c⁻¹ (inv_mem hc) g g.2⟩
  left_inv g := Subtype.ext (by simp [mul_assoc])
  right_inv g := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem cAut_apply (x c : G) (hc : c ∈ centralizer ({x} : Set G)) (g : ↥(Jx x)) :
    ((cAut x c hc g : ↥(Jx x)) : G) = c * g * c⁻¹ := rfl

theorem cAut_cAut (x z : G) (hz : z ∈ centralizer ({x} : Set G)) (hzz : z * z = 1) (g : ↥(Jx x)) :
    cAut x z hz (cAut x z hz g) = g := by
  apply Subtype.ext
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  simp only [cAut_apply, hz']
  calc z * (z * (g : G) * z) * z = (z * z) * g * (z * z) := by simp only [mul_assoc]
    _ = g := by rw [hzz]; simp

theorem cAut_mul_self (x z : G) (hz : z ∈ centralizer ({x} : Set G)) (hzz : z * z = 1) :
    cAut x z hz * cAut x z hz = 1 := by
  ext g
  exact congrArg Subtype.val (cAut_cAut x z hz hzz g)

theorem cAut_map_pPrimeCore (x c : G) (hc : c ∈ centralizer ({x} : Set G)) :
    (pPrimeCore 2 ↥(Jx x)).map (cAut x c hc).toMonoidHom = pPrimeCore 2 ↥(Jx x) :=
  pPrimeCore_map_iso 2 (cAut x c hc)

@[expose] noncomputable def zBar (x z : G) (hz : z ∈ centralizer ({x} : Set G)) :
    MulAut (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) :=
  QuotientGroup.congr (pPrimeCore 2 ↥(Jx x)) (pPrimeCore 2 ↥(Jx x)) (cAut x z hz)
    (cAut_map_pPrimeCore x z hz)

theorem zBar_mk (x z : G) (hz : z ∈ centralizer ({x} : Set G)) (g : ↥(Jx x)) :
    zBar x z hz (g : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ((cAut x z hz g : ↥(Jx x)) :
      ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) :=
  QuotientGroup.congr_mk _ _ _ _ g

theorem zBar_mul_self (x z : G) (hz : z ∈ centralizer ({x} : Set G)) (hzz : z * z = 1) :
    zBar x z hz * zBar x z hz = 1 := by
  ext k
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
  show zBar x z hz (zBar x z hz (g : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))) = g
  rw [zBar_mk, zBar_mk, cAut_cAut x z hz hzz]

omit [Finite G] in
theorem mem_pPrimeCoreOf_Jx_iff (x : G) (g : G) (hg : g ∈ Jx x) :
    g ∈ pPrimeCoreOf 2 (Jx x) ↔ (⟨g, hg⟩ : ↥(Jx x)) ∈ pPrimeCore 2 ↥(Jx x) := by
  constructor
  · rintro ⟨j, hj, hjg⟩
    have : j = ⟨g, hg⟩ := Subtype.ext hjg
    rwa [this] at hj
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

end Action


section Main

variable {G : Type} [Group G] [Finite G]

theorem qdich_of_datum {x z : G} (hzx : z ∈ centralizer ({x} : Set G)) (hzz : z * z = 1)
    (hIJ : Ixz z x ≤ Jx x)
    (hK : (∃ (F : Type) (_ : Field F) (_ : Finite F), L2Field F ∧
        Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* L2 F)) ∨
      Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7)))
    (ht : ∃ t ∈ Ixz z x, orderOf t = 2)
    {q : ℕ} (hq : Odd q) (hq3 : 3 < q)
    (hIL2 : IsL2 (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) (fun r => r = q)) :
    (IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q) ∧
        padicValNat 2 (Nat.card ↥(Jx x)) = padicValNat 2 (Nat.card ↥(Ixz z x))) ∨
      (padicValNat 2 (Nat.card ↥(Jx x)) = padicValNat 2 (Nat.card ↥(Ixz z x)) + 1 ∧
        (IsL2 (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) (fun r => r = q ^ 2) ∨
          (q = 5 ∧ Nonempty ((↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) ≃* alternatingGroup (Fin 7))))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Xs : Subgroup G := centralizer ({x, z} : Set G) with hXs
  have hXsC : Xs ≤ centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert x {z}))
  have hXsz : ∀ g ∈ Xs, z * g = g * z := fun g hg =>
    Subgroup.mem_centralizer_iff.1 hg z (Set.mem_insert_of_mem x rfl)
  have hI : Ixz z x = (pLayer ↥Xs 2).map Xs.subtype := pLayerOf_eq_map_P34 2 Xs
  set Y : Subgroup ↥Xs := (Jx x).subgroupOf Xs with hY
  set N : Subgroup G := pPrimeCoreOf 2 (Jx x) with hN
  set M : Subgroup ↥Xs := N.subgroupOf Xs with hM
  have hNJ : N ≤ Jx x := Subgroup.map_subtype_le _
  have hNN : ∀ (g : ↥Xs) {n : G}, n ∈ N → (g : G) * n * (g : G)⁻¹ ∈ N := by
    intro g n hn
    have hgC : (g : G) ∈ centralizer ({x} : Set G) := hXsC g.2
    obtain ⟨j, hj, rfl⟩ := hn
    have hj' : cAut x g hgC j ∈ pPrimeCore 2 ↥(Jx x) := by
      rw [← cAut_map_pPrimeCore x g hgC]
      exact Subgroup.mem_map_of_mem _ hj
    exact ⟨cAut x g hgC j, hj', rfl⟩
  have hYn : Y.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Jx_normalized x g (hXsC g.2) n hn
  have hMn : M.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hNN g hn
  have hNodd : Odd (Nat.card ↥(pPrimeCore 2 ↥(Jx x))) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥(Jx x)))
  have hModd : Odd (Nat.card ↥M) := by
    have hle : M.map Xs.subtype ≤ N := by
      rintro _ ⟨n, hn, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hn
    have hdvd : Nat.card ↥M ∣ Nat.card ↥N := by
      rw [← Subgroup.card_map_of_injective Xs.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    have hcardN : Nat.card ↥N = Nat.card ↥(pPrimeCore 2 ↥(Jx x)) :=
      Subgroup.card_map_of_injective (Jx x).subtype_injective
    rw [hcardN] at hdvd
    exact Odd.of_dvd_nat hNodd hdvd
  have hMY : M ≤ Y := fun n hn =>
    Subgroup.mem_subgroupOf.2 (hNJ (Subgroup.mem_subgroupOf.1 hn))
  have hL : pLayer ↥Xs 2 ≤ Y := by
    intro l hl
    have h1 : (l : G) ∈ Ixz z x := by rw [hI]; exact ⟨l, hl, rfl⟩
    exact Subgroup.mem_subgroupOf.2 (hIJ h1)
  let θ₀ : ↥Y →* ↥(Jx x) :=
    { toFun := fun y => ⟨((y : ↥Xs) : G), Subgroup.mem_subgroupOf.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let θ : ↥Y →* (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥(Jx x))).comp θ₀
  have hθ : ∀ y : ↥Y, θ y = 1 ↔ ((y : ↥Xs) : ↥Xs) ∈ M := by
    intro y
    show ((θ₀ y : ↥(Jx x)) : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact (mem_pPrimeCoreOf_Jx_iff x _ (Subgroup.mem_subgroupOf.1 y.2)).symm
  have hθfix : ∀ y : ↥Y, zBar x z hzx (θ y) = θ y := by
    intro y
    show zBar x z hzx ((θ₀ y : ↥(Jx x)) : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) =
      ((θ₀ y : ↥(Jx x)) : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))
    rw [zBar_mk]
    congr 1
    apply Subtype.ext
    have h1 := hXsz _ (y : ↥Xs).2
    show z * ((y : ↥Xs) : G) * z⁻¹ = ((y : ↥Xs) : G)
    rw [h1]
    group
  have hlift : ∀ k : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x), zBar x z hzx k = k →
      ∃ y : ↥Y, θ y = k := by
    intro k hk
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective k
    rw [zBar_mk] at hk
    have hg : (cAut x z hzx g)⁻¹ * g ∈ pPrimeCore 2 ↥(Jx x) :=
      (QuotientGroup.eq (s := pPrimeCore 2 ↥(Jx x))).1 hk
    obtain ⟨g', hg'fix, hg'N⟩ := exists_fixed_lift (pPrimeCore 2 ↥(Jx x)) hNodd (cAut x z hzx)
      (cAut_mul_self x z hzx hzz) (cAut_map_pPrimeCore x z hzx) g hg
    have hg'Xs : (g' : G) ∈ Xs := by
      rw [hXs, Subgroup.mem_centralizer_iff]
      intro h hh
      rcases hh with hhx | hhz
      · rw [hhx]
        exact Subgroup.mem_centralizer_iff.1 (Jx_le_centralizer x g'.2) x (Set.mem_singleton x)
      · have hhz' : h = z := hhz
        rw [hhz']
        have h1 : ((cAut x z hzx g' : ↥(Jx x)) : G) = g' := congrArg Subtype.val hg'fix
        rw [cAut_apply] at h1
        calc z * (g' : G) = (z * g' * z⁻¹) * z := by group
          _ = g' * z := by rw [h1]
    refine ⟨⟨⟨g', hg'Xs⟩, Subgroup.mem_subgroupOf.2 g'.2⟩, ?_⟩
    show ((θ₀ ⟨⟨g', hg'Xs⟩, Subgroup.mem_subgroupOf.2 g'.2⟩ : ↥(Jx x)) :
      ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = (g : ↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))
    exact QuotientGroup.eq.2 hg'N
  have ht' : ∃ t ∈ pLayer ↥Xs 2, orderOf t = 2 := by
    obtain ⟨t, htI, ht2⟩ := ht
    rw [hI] at htI
    obtain ⟨s, hs, rfl⟩ := htI
    exact ⟨s, hs, by rw [← Subgroup.orderOf_coe]; exact ht2⟩
  let e₂ : ↥(pLayer ↥Xs 2) ≃* ↥(Ixz z x) :=
    (Subgroup.equivMapOfInjective (pLayer ↥Xs 2) Xs.subtype Xs.subtype_injective).trans
      (MulEquiv.subgroupCongr hI.symm)
  let e₃ : (↥(pLayer ↥Xs 2) ⧸ pPrimeCore 2 ↥(pLayer ↥Xs 2)) ≃*
      (↥(Ixz z x) ⧸ pPrimeCore 2 ↥(Ixz z x)) :=
    QuotientGroup.congr _ _ e₂ (pPrimeCore_map_iso 2 e₂)
  have hIL2' : IsL2 (↥(pLayer ↥Xs 2) ⧸ pPrimeCore 2 ↥(pLayer ↥Xs 2)) (fun r => r = q) :=
    isL2_of_mulEquiv e₃.symm hIL2
  have hcardI : Nat.card ↥(pLayer ↥Xs 2) = Nat.card ↥(Ixz z x) := Nat.card_congr e₂.toEquiv
  have hvJ := padicValNat_card_eq_quotient ↥(Jx x)
  have key := qdich Y M hModd hMY hL hK θ hθ (zBar x z hzx) (zBar_mul_self x z hzx hzz) hθfix
    hlift ht' hq hq3 hIL2'
  rw [hcardI, ← hvJ] at key
  exact key

end Main

end CFSG.GH74.GLS.Stage2.Local.P27.QId
