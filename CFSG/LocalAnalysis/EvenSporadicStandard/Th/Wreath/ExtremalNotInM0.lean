module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.NormalizerDIndexTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SylowNormalSubgroups
public import CFSG.GroupTheory.ElementaryAbelianNormalizerBound
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.SylowCard
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.Wreath.OmegaOneTransvection
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SecondLayer

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThCyc.inf_centralizer_conj_inf_map_eq (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) {T : Subgroup G} (hT : IsPGroup 2 T) {g : G}
    (hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T) :
    (T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom
      = S.map (MulAut.conj g⁻¹).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro y hy
    obtain ⟨l, hl, hyl⟩ := hy.2
    have hyl' : y = g⁻¹ * l * g := by
      rw [← hyl]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hyl'] at hy ⊢
    have hL'mem : g⁻¹ * l * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hl
    have hmap_mem : l ∈ (((T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom) := by
      refine ⟨g⁻¹ * l * g, ⟨hy.1, hL'mem⟩, ?_⟩
      have hg : (MulAut.conj g).toMonoidHom (g⁻¹ * l * g) = l := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [hg]
    have hImgL : (((T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom) ≤ L := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨l, hl, hyl⟩ := hy.2
      have hyl' : y = g⁻¹ * l * g := by
        rw [← hyl]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      rw [hyl']
      have hg : (MulAut.conj g).toMonoidHom (g⁻¹ * l * g) = l := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [hg]
      exact hl
    have hImgP : IsPGroup 2 ↥((((T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom)) := by
      have hYP : IsPGroup 2 ↥((T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊓
          L.map (MulAut.conj g⁻¹).toMonoidHom) :=
        hT.to_le (fun y hy => hy.1.1)
      exact hYP.map (MulAut.conj g).toMonoidHom
    have hSle : S ≤ (((T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj g).toMonoidHom) := by
      intro s hs
      refine ⟨g⁻¹ * s * g, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · change g⁻¹ * s * g ∈ T
        exact hSg s hs
      · refine mem_centralizer_singleton_iff.2 ?_
        calc (g⁻¹ * s * g) * (g⁻¹ * t * g)
            = g⁻¹ * (s * t) * g := by group
          _ = g⁻¹ * (t * s) * g := by rw [H.comm_of_mem_L (W.S_le hs)]
          _ = (g⁻¹ * t * g) * (g⁻¹ * s * g) := by group
      · change g⁻¹ * s * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
          Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom (W.S_le hs)
      · have hg : (MulAut.conj g).toMonoidHom (g⁻¹ * s * g) = s := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
          group
        rw [hg]
    have hsub := W.maximal _ hImgL hImgP hSle
    have hlS : l ∈ S := hsub hmap_mem
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hlS
  · intro y hy
    obtain ⟨s, hs, hys⟩ := hy
    have hys' : y = g⁻¹ * s * g := by
      rw [← hys]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hys']
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · change g⁻¹ * s * g ∈ T
      exact hSg s hs
    · refine mem_centralizer_singleton_iff.2 ?_
      calc (g⁻¹ * s * g) * (g⁻¹ * t * g)
          = g⁻¹ * (s * t) * g := by group
        _ = g⁻¹ * (t * s) * g := by rw [H.comm_of_mem_L (W.S_le hs)]
        _ = (g⁻¹ * t * g) * (g⁻¹ * s * g) := by group
    · change g⁻¹ * s * g ∈ L.map (MulAut.conj g⁻¹).toMonoidHom
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
        Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom (W.S_le hs)

theorem ThCyc.card_inf_centralizer_conj_eq (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) {T : Subgroup G} (hT : IsPGroup 2 T) {g : G} (hu : g⁻¹ * t * g ∈ T)
    (hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T) :
    Nat.card ↥(T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 2 ^ 16 := by
  have hCTL := H.inf_centralizer_conj_inf_map_eq W hT hSg
  have hv : g⁻¹ * t * g ∈ T ⊓ centralizer ({g⁻¹ * t * g} : Set G) :=
    ⟨hu, mem_centralizer_singleton_iff.2 rfl⟩
  have hcard := H.card_eq_two_mul_card_inf (c := g)
    (M := T ⊓ centralizer ({g⁻¹ * t * g} : Set G)) inf_le_right hv
  rw [hCTL, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, W.card_S] at hcard
  rw [hcard]
  norm_num

theorem ThCyc.conj_not_mem_omega1 (H : ThCyc G L R t) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (g : G) :
    g⁻¹ * t * g ∉ omega1 D hD.comm := by
  intro hV
  have huD : g⁻¹ * t * g ∈ D := hV.1
  have hM : D ≤ centralizer ({g⁻¹ * t * g} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (hD.comm d hd (g⁻¹ * t * g) huD)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : IsPGroup 2 D := IsPGroup.of_card (n := 12) hD.card
  have h := H.card_le_of_abelian F.abelian_le hM huD hD.comm h2
  rw [hD.card] at h
  norm_num at h

theorem ThCyc.exists_elementary_normal_inf (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ normalizer (D : Set G)) (hDT : D ≤ T)
    {g : G} (hu : g⁻¹ * t * g ∈ T)
    (hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T) :
    ∃ Y : Subgroup G,
      Y ≤ ((omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊔
            zpowers (g⁻¹ * t * g)) ⊓ L.map (MulAut.conj g⁻¹).toMonoidHom ∧
      Y ≤ S.map (MulAut.conj g⁻¹).toMonoidHom ∧
      (∀ s ∈ S.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y) ∧
      Nat.card Y = Nat.card ↥(omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ∧
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) ∧
      (∀ y ∈ Y, y ^ 2 = 1) := by
  let X : Subgroup G := omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)
  let M : Subgroup G := X ⊔ zpowers (g⁻¹ * t * g)
  let Y : Subgroup G := M ⊓ L.map (MulAut.conj g⁻¹).toMonoidHom
  have huVnot : g⁻¹ * t * g ∉ omega1 D hD.comm :=
    H.conj_not_mem_omega1 hD F g
  have hXleV : X ≤ omega1 D hD.comm := inf_le_left
  have huX : g⁻¹ * t * g ∉ X := fun h => huVnot h.1
  have hXcomm : ∀ x ∈ X, x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x :=
    fun x hx => mem_centralizer_singleton_iff.1 hx.2
  have hXab : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x :=
    fun x hx y hy => H.omega1_comm W W2 hD hx.1 hy.1
  have hXsq : ∀ x ∈ X, x ^ 2 = 1 := fun x hx => hx.1.2
  have hMcent : M ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    refine sup_le ?_ ?_
    · exact inf_le_right
    · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
  have huM : g⁻¹ * t * g ∈ M := mem_sup_right (mem_zpowers _)
  have hMcard : Nat.card M =
      2 * Nat.card ↥(M ⊓ L.map (MulAut.conj g⁻¹).toMonoidHom) :=
    H.card_eq_two_mul_card_inf (c := g) hMcent huM
  have hXsup : Nat.card ↥(X ⊔ zpowers (g⁻¹ * t * g)) = 2 * Nat.card X :=
    H.card_sup_conj (c := g) (K := X) hXcomm huX
  have h1 : Nat.card M = 2 * Nat.card X := hXsup
  have hYcard : Nat.card Y =
      Nat.card ↥(omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
    dsimp only [Y, X] at h1 hMcard ⊢
    omega
  have hMleCT : M ≤ T ⊓ centralizer ({g⁻¹ * t * g} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      exact ⟨hDT hx.1.1, hx.2⟩
    · exact le_inf (zpowers_le.2 hu)
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
  have hYleS' : Y ≤ S.map (MulAut.conj g⁻¹).toMonoidHom := by
    dsimp only [Y]
    rw [← H.inf_centralizer_conj_inf_map_eq W hT hSg]
    exact le_inf (inf_le_left.trans hMleCT) inf_le_right
  have hS'leL' : S.map (MulAut.conj g⁻¹).toMonoidHom ≤
      L.map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) W.S_le
  have hS'leT : S.map (MulAut.conj g⁻¹).toMonoidHom ≤ T := by
    rintro s ⟨s0, hs0, hys⟩
    have hys' : s = g⁻¹ * s0 * g := by
      rw [← hys]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hys']
    change g⁻¹ * s0 * g ∈ T
    exact hSg s0 hs0
  have hS'comm_u : ∀ s ∈ S.map (MulAut.conj g⁻¹).toMonoidHom,
      s * (g⁻¹ * t * g) = (g⁻¹ * t * g) * s := by
    rintro s ⟨s0, hs0, hys⟩
    have hys' : s = g⁻¹ * s0 * g := by
      rw [← hys]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hys']
    calc (g⁻¹ * s0 * g) * (g⁻¹ * t * g)
        = g⁻¹ * (s0 * t) * g := by group
      _ = g⁻¹ * (t * s0) * g := by rw [H.comm_of_mem_L (W.S_le hs0)]
      _ = (g⁻¹ * t * g) * (g⁻¹ * s0 * g) := by group
  have hconjzu : ∀ s : G, s * (g⁻¹ * t * g) = (g⁻¹ * t * g) * s →
      ∀ r ∈ zpowers (g⁻¹ * t * g), s * r * s⁻¹ ∈ zpowers (g⁻¹ * t * g) := by
    intro s hsu r hr
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    have hsu' : (MulAut.conj s).toMonoidHom (g⁻¹ * t * g) = g⁻¹ * t * g := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc s * (g⁻¹ * t * g) * s⁻¹ = ((g⁻¹ * t * g) * s) * s⁻¹ := by rw [hsu]
        _ = g⁻¹ * t * g := by group
    have hmap := map_zpow (MulAut.conj s).toMonoidHom (g⁻¹ * t * g) k
    rw [hsu'] at hmap
    have hval : s * (g⁻¹ * t * g) ^ k * s⁻¹ = (g⁻¹ * t * g) ^ k := by
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hmap
    rw [hval]
    exact (zpowers (g⁻¹ * t * g)).zpow_mem (mem_zpowers (g⁻¹ * t * g)) k
  have hcommX : zpowers (g⁻¹ * t * g) ≤ centralizer (X : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun y hy => hXcomm y hy
  have hYn : ∀ s ∈ S.map (MulAut.conj g⁻¹).toMonoidHom, ∀ y ∈ Y, s * y * s⁻¹ ∈ Y := by
    intro s hs y hy
    have hsT : s ∈ T := hS'leT hs
    have hsNV : s ∈ normalizer (omega1 D hD.comm : Set G) :=
      ThCyc.normalizer_D_le_normalizer_omega1 hD (hTM hsT)
    have hsu : s * (g⁻¹ * t * g) = (g⁻¹ * t * g) * s := hS'comm_u s hs
    have hsuinv : s⁻¹ * (g⁻¹ * t * g) = (g⁻¹ * t * g) * s⁻¹ := by
      calc s⁻¹ * (g⁻¹ * t * g) = s⁻¹ * ((g⁻¹ * t * g) * s) * s⁻¹ := by group
        _ = s⁻¹ * (s * (g⁻¹ * t * g)) * s⁻¹ := by rw [← hsu]
        _ = (g⁻¹ * t * g) * s⁻¹ := by group
    have hyM : y ∈ M := by
      dsimp only [Y] at hy
      exact hy.1
    obtain ⟨x, hx, r, hr, hxy⟩ := exists_mul_of_mem_sup hcommX hyM
    refine ⟨?_, ?_⟩
    · rw [hxy, show s * (x * r) * s⁻¹ = (s * x * s⁻¹) * (s * r * s⁻¹) from by group]
      refine mul_mem_sup ?_ ?_
      · refine ⟨(mem_normalizer_iff.1 hsNV x).1 hx.1, ?_⟩
        refine mem_centralizer_singleton_iff.2 ?_
        calc (s * x * s⁻¹) * (g⁻¹ * t * g)
            = s * (x * (s⁻¹ * (g⁻¹ * t * g) * s)) * s⁻¹ := by group
          _ = s * (x * ((g⁻¹ * t * g) * s⁻¹ * s)) * s⁻¹ := by rw [hsuinv]
          _ = s * (x * (g⁻¹ * t * g)) * s⁻¹ := by group
          _ = s * ((g⁻¹ * t * g) * x) * s⁻¹ := by
              rw [mem_centralizer_singleton_iff.1 hx.2]
          _ = (s * (g⁻¹ * t * g)) * x * s⁻¹ := by group
          _ = ((g⁻¹ * t * g) * s) * x * s⁻¹ := by rw [hsu]
          _ = (g⁻¹ * t * g) * (s * x * s⁻¹) := by group
      · exact hconjzu s hsu r hr
    · exact (L.map (MulAut.conj g⁻¹).toMonoidHom).mul_mem
        ((L.map (MulAut.conj g⁻¹).toMonoidHom).mul_mem (hS'leL' hs) hy.2)
        ((L.map (MulAut.conj g⁻¹).toMonoidHom).inv_mem (hS'leL' hs))
  have hMcomm : ∀ a ∈ M, ∀ c ∈ M, a * c = c * a :=
    SylowEnd.sup_zpowers_comm hXcomm hXab
  have hMsq : ∀ a ∈ M, a ^ 2 = 1 :=
    SylowEnd.sup_zpowers_sq (H.conj_sq g) hXcomm hXsq
  exact ⟨Y, le_refl Y, hYleS', hYn, hYcard,
    fun x hx y hy => hMcomm x hx.1 y hy.1, fun y hy => hMsq y hy.1⟩

theorem ThCyc.false_of_conj_mem_M0 (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTM : T ≤ normalizer (D : Set G)) (hDT : D ≤ T)
    {g : G} (hu : g⁻¹ * t * g ∈ T ⊓ M0 L A D hD.comm)
    (hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T) : False := by
  classical
  have hf3 : ∀ {m n : G}, n ∈ L ⊓ normalizer (A : Set G) →
      (∀ v ∈ omega1 D hD.comm, m * v * m⁻¹ = n * v * n⁻¹) →
      Nat.card ↥(A ⊓ centralizer ({m} : Set G)) = 8 →
      Nat.card ↥(omega1 D hD.comm ⊓ centralizer ({m} : Set G)) = 2 ^ 6 :=
    fun hn hmn hfix => H.card_omega1_inf_centralizer_of_conj_eq W W2 hD h4 hb hn hmn hfix
  have hu2 : (g⁻¹ * t * g) ^ 2 = 1 := H.conj_sq g
  have huT : g⁻¹ * t * g ∈ T := hu.1
  have huM0 : g⁻¹ * t * g ∈ M0 L A D hD.comm := hu.2
  have huVnot : g⁻¹ * t * g ∉ omega1 D hD.comm :=
    H.conj_not_mem_omega1 hD F g
  have hA_N : g⁻¹ * t * g ∈ normalizer (A : Set G) :=
    H.normalizer_D_le_normalizer_A W W2 hD h4 (hTM huT)
  have hV_N : g⁻¹ * t * g ∈ normalizer (omega1 D hD.comm : Set G) :=
    ThCyc.normalizer_D_le_normalizer_omega1 hD (hTM huT)
  haveI hAelem : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.two_of_forall_mul_self W.A_comm
      (fun a ha => by simpa [pow_two] using W.A_sq a ha)
  have hAsq := CFSG.GroupTheory.card_le_card_inf_centralizer_sq (Y := A)
    (x := g⁻¹ * t * g) hA_N (by rw [hu2]; exact Subgroup.one_mem _)
  have hAge4 : 4 ≤ Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
    rw [W.A_card] at hAsq
    nlinarith
  have hAdvd : Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ∣ 16 := by
    let Ysub : Subgroup ↥A := (A ⊓ centralizer ({g⁻¹ * t * g} : Set G)).subgroupOf A
    have hYsub : Nat.card ↥Ysub =
        Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h := Subgroup.card_subgroup_dvd_card Ysub
    rwa [W.A_card, hYsub] at h
  haveI hVele : IsElementaryAbelian 2 (omega1 D hD.comm) :=
    IsElementaryAbelian.two_of_forall_mul_self
      (fun a ha b hb => H.omega1_comm W W2 hD ha hb)
      (fun a ha => by simpa [pow_two] using ha.2)
  have hVsq := CFSG.GroupTheory.card_le_card_inf_centralizer_sq
    (Y := omega1 D hD.comm) (x := g⁻¹ * t * g) hV_N
    (by rw [hu2]; exact Subgroup.one_mem _)
  have hX16 : 16 ≤ Nat.card ↥(omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)) := by
    rw [H.card_omega1 W W2 hD (fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd)] at hVsq
    nlinarith
  obtain ⟨Y, hYle, hYleS', hYn, hYcard, hYcomm, hYsq⟩ :=
    H.exists_elementary_normal_inf W W2 hD F hT hTM hDT hu.1 hSg
  set k : ℕ := Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) with hk
  have hk_ge : 4 ≤ k := by rw [hk]; exact hAge4
  have hk_dvd : k ∣ 16 := by rw [hk]; exact hAdvd
  have hk_cases : k = 4 ∨ k = 8 ∨ k = 16 := by
    have hk_le : k ≤ 16 := Nat.le_of_dvd (by norm_num) hk_dvd
    have hk_dvd' : k ∣ 2 ^ 4 := by simpa using hk_dvd
    obtain ⟨j, hjle, hjk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk_dvd'
    have hj2 : 2 ≤ j := by
      have h : 2 ^ 2 ≤ 2 ^ j := by
        rw [← hjk]
        norm_num
        exact hk_ge
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    have hj4 : j ≤ 4 := by
      have h : 2 ^ j ≤ 2 ^ 4 := by
        rw [← hjk]
        norm_num
        exact hk_le
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
    interval_cases j
    · left; norm_num at hjk; exact hjk
    · right; left; norm_num at hjk; exact hjk
    · right; right; norm_num at hjk; exact hjk
  rcases hk_cases with hk4 | hk8 | hk16
  ·
    have hA4 : Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 4 := by
      rw [← hk]; exact hk4
    let CT : Subgroup G := T ⊓ centralizer ({g⁻¹ * t * g} : Set G)
    let K : Subgroup G := normalizer (D : Set G) ⊓
      centralizer (omega1 D hD.comm : Set G)
    let Qu : Subgroup G := CT ⊓ K
    let CA : Subgroup G := CT ⊓ centralizer (A : Set G)
    have hCTcard : Nat.card CT = 2 ^ 16 := by
      simpa only [CT] using H.card_inf_centralizer_conj_eq W hT hu.1 hSg
    have hCTL : CT ⊓ L.map (MulAut.conj g⁻¹).toMonoidHom =
        S.map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [CT] using H.inf_centralizer_conj_inf_map_eq W hT hSg
    have hCT_pgroup : IsPGroup 2 CT := hT.to_le (fun x hx => hx.1)
    have hCTN : CT ≤ normalizer (D : Set G) := fun x hx => hTM hx.1
    have hCT_N_A : CT ≤ normalizer (A : Set G) :=
      hCTN.trans (H.normalizer_D_le_normalizer_A W W2 hD h4)
    have huCT : g⁻¹ * t * g ∈ CT :=
      ⟨huT, mem_centralizer_singleton_iff.2 rfl⟩
    have huQu : g⁻¹ * t * g ∉ Qu := by
      intro h
      have huK : g⁻¹ * t * g ∈ K := h.2
      have huCV : g⁻¹ * t * g ∈ centralizer (omega1 D hD.comm : Set G) := huK.2
      have hAleC : A ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
        intro a ha
        exact mem_centralizer_singleton_iff.2
          (mem_centralizer_iff.1 huCV a (H.A_le_omega1 W W2 hD ha))
      have hcardA : Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 16 := by
        rw [inf_of_le_left hAleC, W.A_card]
      rw [hA4] at hcardA
      norm_num at hcardA
    have hQu_comm_u : ∀ q ∈ Qu, q * (g⁻¹ * t * g) = (g⁻¹ * t * g) * q := by
      intro q hq
      exact mem_centralizer_singleton_iff.1 hq.1.2
    have hQusup : Nat.card ↥(Qu ⊔ zpowers (g⁻¹ * t * g)) = 2 * Nat.card Qu :=
      H.card_sup_conj (c := g) (K := Qu) hQu_comm_u huQu
    have hQusup_cent : Qu ⊔ zpowers (g⁻¹ * t * g) ≤
        centralizer ({g⁻¹ * t * g} : Set G) := by
      refine sup_le ?_ ?_
      · intro q hq
        exact hq.1.2
      · exact zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)
    have huQusup : g⁻¹ * t * g ∈ Qu ⊔ zpowers (g⁻¹ * t * g) :=
      mem_sup_right (mem_zpowers _)
    have hQusup_card : Nat.card ↥(Qu ⊔ zpowers (g⁻¹ * t * g)) =
        2 * Nat.card ↥((Qu ⊔ zpowers (g⁻¹ * t * g)) ⊓
          L.map (MulAut.conj g⁻¹).toMonoidHom) :=
      H.card_eq_two_mul_card_inf (c := g) hQusup_cent huQusup
    have hQu_eq : Nat.card Qu = Nat.card ↥((Qu ⊔ zpowers (g⁻¹ * t * g)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom) := by
      omega
    have hQuSup_le_CT : Qu ⊔ zpowers (g⁻¹ * t * g) ≤ CT := by
      refine sup_le ?_ ?_
      · exact inf_le_left
      · exact zpowers_le.2 huCT
    let M : Subgroup G :=
      (omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ⊔
        zpowers (g⁻¹ * t * g)
    have hYleM : Y ≤ M := hYle.trans inf_le_left
    have hQuSup_centM : Qu ⊔ zpowers (g⁻¹ * t * g) ≤ centralizer (M : Set G) := by
      refine sup_le ?_ ?_
      · intro q hq
        have hqCT : q ∈ CT := hq.1
        have hqK : q ∈ K := hq.2
        have hqX : ∀ x ∈ omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G),
            x * q = q * x := fun x hx => mem_centralizer_iff.1 hqK.2 x hx.1
        have hquart : q * (g⁻¹ * t * g) = (g⁻¹ * t * g) * q :=
          mem_centralizer_singleton_iff.1 hqCT.2
        have hMX : (omega1 D hD.comm ⊓ centralizer ({g⁻¹ * t * g} : Set G)) ≤
            centralizer ({q} : Set G) := by
          intro x hx
          exact mem_centralizer_singleton_iff.2 (hqX x hx)
        have hMZ : zpowers (g⁻¹ * t * g) ≤ centralizer ({q} : Set G) :=
          zpowers_le.2 (mem_centralizer_singleton_iff.2 hquart.symm)
        have hMle : M ≤ centralizer ({q} : Set G) := sup_le hMX hMZ
        exact mem_centralizer_iff.2 fun m hm =>
          mem_centralizer_singleton_iff.1 (hMle hm)
      · rw [zpowers_le]
        have hMleC : M ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
          refine sup_le inf_le_right (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
        exact mem_centralizer_iff.2 fun m hm =>
          mem_centralizer_singleton_iff.1 (hMleC hm)
    have hQuSup_le_CY : (Qu ⊔ zpowers (g⁻¹ * t * g)) ⊓
        L.map (MulAut.conj g⁻¹).toMonoidHom ≤
        S.map (MulAut.conj g⁻¹).toMonoidHom ⊓ centralizer (Y : Set G) := by
      refine le_inf ?_ ?_
      · rw [← hCTL]
        exact le_inf (inf_le_left.trans hQuSup_le_CT) inf_le_right
      · intro z hz
        have hzCM : z ∈ centralizer (M : Set G) := hQuSup_centM hz.1
        exact mem_centralizer_iff.2 fun y hy =>
          mem_centralizer_iff.1 hzCM y (hYleM hy)
    have hY16 : 16 ≤ Nat.card Y := by rw [hYcard]; exact hX16
    have hSYbound := W.card_inf_centralizer_le_of_normal_map (g⁻¹) hYleS' hYn hY16
    have hQuBound : Nat.card Qu ≤ 2 ^ 9 := by
      rw [hQu_eq]
      exact (Subgroup.card_le_of_le hQuSup_le_CY).trans hSYbound
    have hQuCA : Qu ≤ CA := by
      refine le_inf inf_le_left ?_
      intro q hq
      exact mem_centralizer_iff.2 fun a ha =>
        mem_centralizer_iff.1 hq.2.2 a (H.A_le_omega1 W W2 hD ha)
    have hCA_le : Nat.card CA ≤ 2 * Nat.card Qu := by
      by_cases hex : ∃ c₀ ∈ CA, ∀ v ∈ omega1 D hD.comm,
          c₀ * v * c₀⁻¹ = t * v * t⁻¹
      · obtain ⟨c₀, hc₀CA, hc₀t⟩ := hex
        let f : Qu × Bool → CA := fun qr =>
          match qr.2 with
          | false => ⟨(qr.1 : G), hQuCA qr.1.2⟩
          | true => ⟨(qr.1 : G) * c₀, CA.mul_mem (hQuCA qr.1.2) hc₀CA⟩
        have hfsurj : Function.Surjective f := by
          intro c
          have hcCA : (c : G) ∈ CA := c.2
          have hcCT : (c : G) ∈ CT := hcCA.1
          have hcA : (c : G) ∈ centralizer (A : Set G) := hcCA.2
          have hcD : (c : G) ∈ normalizer (D : Set G) := hTM hcCT.1
          have hcA' : ∀ a ∈ A, (c : G) * a * (c : G)⁻¹ = a := by
            intro a ha
            have h := mem_centralizer_iff.1 hcA a ha
            calc (c : G) * a * (c : G)⁻¹ = (a * (c : G)) * (c : G)⁻¹ := by rw [← h]
              _ = a := by group
          rcases H.conj_omega1_eq_or_of_mem_normalizer_D W W2 hD h4 hb hcD hcA' with
            htriv | ht
          · have hcCV : (c : G) ∈ centralizer (omega1 D hD.comm : Set G) :=
              mem_centralizer_iff.2 fun v hv => (mul_inv_eq_iff_eq_mul.mp (htriv v hv)).symm
            have hcQu : (c : G) ∈ Qu := ⟨hcCT, ⟨hcD, hcCV⟩⟩
            refine ⟨((⟨(c : G), hcQu⟩ : Qu), false), ?_⟩
            apply Subtype.ext
            simp [f]
          · have hc₀CT : c₀ ∈ CT := hc₀CA.1
            have hc₀D : c₀ ∈ normalizer (D : Set G) := hTM hc₀CT.1
            have hc₀NV : c₀ ∈ normalizer (omega1 D hD.comm : Set G) :=
              ThCyc.normalizer_D_le_normalizer_omega1 hD hc₀D
            have hcc₀ : ∀ v ∈ omega1 D hD.comm,
                ((c : G) * c₀⁻¹) * v * ((c : G) * c₀⁻¹)⁻¹ = v := by
              intro v hv
              have hv' : t * v * t⁻¹ ∈ omega1 D hD.comm :=
                H.t_conj_mem_omega1 W W2 hD hv
              have hc₀inv_v : c₀⁻¹ * v * c₀ = t * v * t⁻¹ := by
                have hw : c₀⁻¹ * v * c₀ ∈ omega1 D hD.comm := by
                  simpa using (mem_normalizer_iff.1
                    ((normalizer (omega1 D hD.comm : Set G)).inv_mem hc₀NV) v).1 hv
                have h := hc₀t (c₀⁻¹ * v * c₀) hw
                have hsimp : c₀ * (c₀⁻¹ * v * c₀) * c₀⁻¹ = v := by group
                rw [hsimp] at h
                have htinv : t⁻¹ = t :=
                  inv_eq_of_mul_eq_one_right (by rw [← sq]; exact H.sq_t)
                calc c₀⁻¹ * v * c₀ = t⁻¹ * v * t := by
                      conv_rhs => rw [h]
                      group
                  _ = t * v * t⁻¹ := by rw [htinv]
              calc ((c : G) * c₀⁻¹) * v * ((c : G) * c₀⁻¹)⁻¹
                  = (c : G) * (c₀⁻¹ * v * c₀) * (c : G)⁻¹ := by group
                _ = (c : G) * (t * v * t⁻¹) * (c : G)⁻¹ := by rw [hc₀inv_v]
                _ = t * (t * v * t⁻¹) * t⁻¹ := ht _ hv'
                _ = v := by
                    have ht2 : t * t = 1 := by rw [← sq]; exact H.sq_t
                    have htinv2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev, ht2, inv_one]
                    calc t * (t * v * t⁻¹) * t⁻¹ = (t * t) * v * (t⁻¹ * t⁻¹) := by group
                      _ = v := by rw [ht2, htinv2]; group
            have hq : (c : G) * c₀⁻¹ ∈ Qu :=
              ⟨CT.mul_mem hcCT (CT.inv_mem hc₀CT),
                ⟨(normalizer (D : Set G)).mul_mem hcD
                    ((normalizer (D : Set G)).inv_mem hc₀D),
                  mem_centralizer_iff.2 fun v hv => (mul_inv_eq_iff_eq_mul.mp (hcc₀ v hv)).symm⟩⟩
            refine ⟨((⟨(c : G) * c₀⁻¹, hq⟩ : Qu), true), ?_⟩
            apply Subtype.ext
            dsimp only [f]
            group
        have hcardle : Nat.card CA ≤ Nat.card Qu * 2 := by
          have h := Nat.card_le_card_of_surjective f hfsurj
          rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h
        calc Nat.card CA ≤ Nat.card Qu * 2 := hcardle
          _ = 2 * Nat.card Qu := Nat.mul_comm _ _
      · have hCAleQu : CA ≤ Qu := by
          intro c hcCA
          have hcCT : (c : G) ∈ CT := hcCA.1
          have hcA : (c : G) ∈ centralizer (A : Set G) := hcCA.2
          have hcD : (c : G) ∈ normalizer (D : Set G) := hTM hcCT.1
          have hcA' : ∀ a ∈ A, (c : G) * a * (c : G)⁻¹ = a := by
            intro a ha
            have h := mem_centralizer_iff.1 hcA a ha
            calc (c : G) * a * (c : G)⁻¹ = (a * (c : G)) * (c : G)⁻¹ := by rw [← h]
              _ = a := by group
          have htriv : ∀ v ∈ omega1 D hD.comm, (c : G) * v * (c : G)⁻¹ = v := by
            rcases H.conj_omega1_eq_or_of_mem_normalizer_D W W2 hD h4 hb hcD hcA' with
              h | h
            · exact h
            · exact absurd ⟨c, hcCA, h⟩ hex
          have hcCV : (c : G) ∈ centralizer (omega1 D hD.comm : Set G) :=
            mem_centralizer_iff.2 fun v hv => (mul_inv_eq_iff_eq_mul.mp (htriv v hv)).symm
          exact ⟨hcCT, ⟨hcD, hcCV⟩⟩
        have h := Subgroup.card_le_of_le hCAleQu
        omega
    have hCT_A : ∀ x ∈ CT, ∀ a ∈ A, x * a * x⁻¹ ∈ A :=
      fun x hx a ha => (mem_normalizer_iff.1 (hCT_N_A hx) a).1 ha
    have hu_A : ∀ a ∈ A, (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ ∈ A :=
      fun a ha => (mem_normalizer_iff.1 hA_N a).1 ha
    have hu_sq_cent : ∀ a ∈ A,
        (g⁻¹ * t * g) ^ 2 * a * ((g⁻¹ * t * g) ^ 2)⁻¹ = a := by
      intro a ha
      rw [hu2]
      group
    have hCT_u : ∀ x ∈ CT, ∀ a ∈ A,
        (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) * a *
          (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹)⁻¹ = a := by
      intro x hx a ha
      have hxu : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x :=
        mem_centralizer_singleton_iff.1 hx.2
      have hxconj : x * (g⁻¹ * t * g) * x⁻¹ = g⁻¹ * t * g := by
        calc x * (g⁻¹ * t * g) * x⁻¹ = ((g⁻¹ * t * g) * x) * x⁻¹ := by rw [hxu]
          _ = g⁻¹ * t * g := by group
      have h1 : x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹ = 1 := by
        rw [hxconj]; group
      rw [h1]
      group
    have hCTbound : Nat.card CT ≤ 32 * Nat.card CA := by
      have h := CFSG.GroupTheory.card_le_two_pow_mul_of_centralizes_involution_mod
        (A := A) (P := CT) (k := 2) (u := g⁻¹ * t * g)
        (by simpa using W.A_card) hCT_pgroup hCT_N_A hA_N
        (by rw [hu2]; exact Subgroup.one_mem _) (by simpa using hA4)
        (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun a ha => by
          have h := hCT_u x hx a ha
          have h' : (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) * a =
              a * (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) := by
            calc (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) * a
                = ((x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) * a *
                    (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹)⁻¹) *
                    (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) := by group
              _ = a * (x * (g⁻¹ * t * g) * x⁻¹ * (g⁻¹ * t * g)⁻¹) := by rw [h]
          exact h'.symm))
      norm_num at h
      exact h
    have hCTle : Nat.card CT ≤ 2 ^ 15 := by
      calc Nat.card CT ≤ 32 * Nat.card CA := hCTbound
        _ ≤ 32 * (2 * Nat.card Qu) := Nat.mul_le_mul_left 32 hCA_le
        _ ≤ 32 * (2 * 2 ^ 9) := Nat.mul_le_mul_left 32 (Nat.mul_le_mul_left 2 hQuBound)
        _ = 2 ^ 15 := by norm_num
    rw [hCTcard] at hCTle
    norm_num at hCTle
  ·
    have hA8 : Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 8 := by
      rw [← hk]; exact hk8
    obtain ⟨n, hn, hact, -, -⟩ :=
      H.exists_mem_inf_normalizer_centralizer_eq_of_mem_M0 W W2 hD huM0
    have hX8 : Nat.card ↥(omega1 D hD.comm ⊓
        centralizer ({g⁻¹ * t * g} : Set G)) = 2 ^ 6 :=
      hf3 hn hact hA8
    have hY8 : Nat.card Y = 2 ^ 6 := by
      rw [hYcard, hX8]
    have hY16 : 16 ≤ Nat.card Y := by rw [hY8]; norm_num
    have hle32 := W2.card_le_of_normal_elementary_map W (g⁻¹) hYleS' hYn hY16 hYcomm hYsq
    rw [hY8] at hle32
    norm_num at hle32
  ·
    have hA16 : Nat.card ↥(A ⊓ centralizer ({g⁻¹ * t * g} : Set G)) = 16 := by
      rw [← hk]; exact hk16
    have hAleC : A ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
      have hAeq : A ⊓ centralizer ({g⁻¹ * t * g} : Set G) = A :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hA16, W.A_card])
      exact hAeq ▸ inf_le_right
    have hAcent : ∀ a ∈ A, (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹ = a := by
      intro a ha
      have hu : (g⁻¹ * t * g) * a = a * (g⁻¹ * t * g) :=
        (mem_centralizer_singleton_iff.1 (hAleC ha)).symm
      calc (g⁻¹ * t * g) * a * (g⁻¹ * t * g)⁻¹
          = (a * (g⁻¹ * t * g)) * (g⁻¹ * t * g)⁻¹ := by rw [hu]
        _ = a := by group
    have huV : ∀ v ∈ omega1 D hD.comm,
        (g⁻¹ * t * g) * v * (g⁻¹ * t * g)⁻¹ = v :=
      H.centralizes_omega1_of_mem_M0 W W2 hD hb huM0 hAcent
    have hle : omega1 D hD.comm ≤ centralizer ({g⁻¹ * t * g} : Set G) := fun v hv =>
      mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.mp (huV v hv)).symm
    have hlt := H.card_lt_of_elementary (c := g) F.elementary_le hle
      (fun x hx y hy => H.omega1_comm W W2 hD hx hy) (fun x hx => hx.2) huVnot
    rw [H.card_omega1 W W2 hD (fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd)] at hlt
    norm_num at hlt

theorem ThCyc.false_of_sylow_le_normalizer_D (H : ThCyc G L R t)
    (W : ThLocalIn L S A B z) (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)
    (F : SylowFacts L S B Aa)
    (h4 : ∀ d ∈ D, d ^ 4 = 1) (hb : ∀ d ∈ D, b * d * b⁻¹ = d⁻¹)
    {T : Subgroup G} (hT : IsPGroup 2 T) (hTidx : ¬ 2 ∣ T.index)
    (hST : S ⊔ zpowers t ≤ T) (hTM : T ≤ normalizer (D : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htT : t ∈ T := hST (mem_sup_right (mem_zpowers t))
  have hD2 : IsPGroup 2 D := IsPGroup.of_card (n := 12) hD.card
  have hX : IsPGroup 2 ↥(T ⊔ D) := hT.to_sup_of_normal_right' hD2 hTM
  have hTeq : T ⊔ D = T := by
    have h := (hT.toSylow hTidx).is_maximal' hX le_sup_left
    rwa [IsPGroup.toSylow_coe] at h
  have hDT : D ≤ T := hTeq ▸ le_sup_right
  have := H.simple
  have hG := not_exists_normal_index_two_of_nonabelian H.nonabelian
  obtain ⟨g, hgQ, -, hconj⟩ := exists_extremal_conj_of_cyclic hG hT hTidx
    (H.conj_mem_inf_M0 W W2 hD h4 hb hTM)
    (H.exists_zpow_inv_mul_mem_inf_M0 W W2 hD h4 hb hTM htT)
    htT (H.t_not_mem_inf_M0 W W2 hD h4 hb) H.sq_t
  have hSg : ∀ s ∈ S, g⁻¹ * s * g ∈ T := by
    intro s hs
    have hsc : s ∈ T ⊓ centralizer ({t} : Set G) :=
      ⟨hST (mem_sup_left hs),
        mem_centralizer_singleton_iff.2 (H.comm_of_mem_L (W.S_le hs)).symm⟩
    exact (hconj s hsc).1
  exact H.false_of_conj_mem_M0 W W2 hD F h4 hb hT hTM hDT hgQ hSg

end CFSG.EvenSporadicStandard.ThStd
