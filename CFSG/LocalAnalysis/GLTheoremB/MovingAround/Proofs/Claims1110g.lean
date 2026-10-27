module

public import Certificates.Certificate111001
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
import CFSG.Models.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveGen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Fi22FiveMaxOrbits
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110f
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.SporFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110g

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open CFSG.AGLEmbedding.KFactProofs.Fi22Five CFSG.AGLEmbedding.KFactProofs.Fi22Five.D4
open CFSG.Certificates CFSG.Certificates.Native CFSG.EvenSmallLie.OmegaEight
open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.Open (GLBCore IsElemAbelian GLAPLayer)
open CFSG.HardMathSupport.Solomon.LocalBalance (IsFiTwentyTwo Fi22Facts)

attribute [local irreducible] ordList ordA posA

section Derived

theorem iInf_derivedSeries_eq {A : Type*} [Group A] (N : Subgroup A) [N.Normal] (hN : ⁅N, N⁆ = N)
    [Group.IsSolvable (A ⧸ N)] : (⨅ n : ℕ, derivedSeries A n) = N := by
  apply le_antisymm
  · obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := A ⧸ N)
    have h1 := map_derivedSeries_eq (QuotientGroup.mk'_surjective N) n
    rw [hn] at h1
    refine (iInf_le _ n).trans ?_
    intro g hg
    have h2 : QuotientGroup.mk' N g ∈ (derivedSeries A n).map (QuotientGroup.mk' N) :=
      Subgroup.mem_map_of_mem _ hg
    rw [h1, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · refine le_iInf fun n => ?_
    induction n with
    | zero => exact le_top
    | succ n ih =>
      rw [derivedSeries_succ, ← hN]
      exact Subgroup.commutator_mono ih ih

theorem derivedInf_eq_of_mulEquiv {X A : Type*} [Group X] [Group A] (H : Subgroup X) (θ : ↥H ≃* A) :
    derivedInf H = ((⨅ n : ℕ, derivedSeries A n).comap θ.toMonoidHom).map H.subtype := by
  have hser : ∀ n, derivedSeries ↥H n = (derivedSeries A n).comap θ.toMonoidHom := fun n => by
    rw [← map_derivedSeries_eq (f := θ.symm.toMonoidHom) θ.symm.surjective n,
      Subgroup.comap_equiv_eq_map_symm']
  unfold derivedInf
  simp_rw [hser]
  rw [Subgroup.comap_iInf, Subgroup.map_iInf _ H.subtype_injective]

end Derived

section S0

@[expose] def S0 : Set (Fin 3510) := {p | posA[p.val]! < 360}

@[expose] def ordF (j : Fin 360) : Fin 3510 := ⟨ordA[j.val]! % 3510, Nat.mod_lt _ (by norm_num)⟩

@[expose] def posF (p : Fin 3510) : Fin 360 := ⟨posA[p.val]! % 360, Nat.mod_lt _ (by norm_num)⟩

@[expose] def stabS0 : Subgroup (Equiv.Perm (Fin 3510)) where
  carrier := {g | ∀ p : Fin 3510, p ∈ S0 ↔ g p ∈ S0}
  mul_mem' := fun {g h} hg hh p => (hh p).trans (hg (h p))
  one_mem' := fun _ => Iff.rfl
  inv_mem' := fun {g} hg p => by
    have := hg (g⁻¹ p)
    rw [show g (g⁻¹ p) = p by simp] at this
    exact this.symm

theorem d4_facts : (ordList.length = 360 ∧ ordList.Nodup ∧ ∀ p ∈ ordList, p < 3510) ∧
    (∀ t ∈ [xA, yA, hA, n1A, n2A, zA], ∀ g : Equiv.Perm (Fin 3510), Rep 3510 t g →
      ∀ p : Fin 3510, (p : ℕ) ∈ ordList → ((g p : Fin 3510) : ℕ) ∈ ordList) ∧
    (∀ g : Equiv.Perm (Fin 3510), Rep 3510 (evalW [1]) g →
      ∃ p : Fin 3510, (p : ℕ) ∈ ordList ∧ ((g p : Fin 3510) : ℕ) ∉ ordList) ∧
    (∀ t ∈ [g1A, g2A], ∀ g : Equiv.Perm (Fin 3510), Rep 3510 t g →
      ∀ σ : Equiv.Perm (Fin 360),
        (∀ (k : Fin 360) (p : Fin 3510), (p : ℕ) = ordList[(k : ℕ)]! →
          ((g p : Fin 3510) : ℕ) = ordList[((σ k : Fin 360) : ℕ)]!) → σ ∈ autT) ∧
    (∀ X Y : Equiv.Perm (Fin 3510), Rep 3510 xA X → Rep 3510 yA Y →
      ∀ i j : ℕ, i < 5 → j < 5 → (i ≠ 0 ∨ j ≠ 0) →
        ∃ p : Fin 3510, (p : ℕ) ∈ ordList ∧ (X ^ i * Y ^ j) p ≠ p) :=
  Certificates.certificate111001

theorem ordA_get {j : ℕ} (hj : j < ordList.length) : ordA[j]! = ordList[j] := by
  rw [ordA, getElem!_pos ordList.toArray j (by simpa using hj)]
  simp

theorem posA_get {p : ℕ} (hp : p < 3510) : posA[p]! = ordList.idxOf p := by
  rw [posA, getElem!_ofFn_nat _ hp]

theorem ordOK_spec : (∀ j < 360, ordA[j]! < 3510 ∧ posA[ordA[j]!]! = j) ∧
    ∀ p < 3510, posA[p]! < 360 → ordA[posA[p]!]! = p := by
  obtain ⟨hl, hnd, hlt⟩ := d4_facts.1
  refine ⟨fun j hj => ?_, fun p hp hpos => ?_⟩
  · have hj' : j < ordList.length := by rw [hl]; exact hj
    have h1 : ordList[j] < 3510 := hlt _ (List.getElem_mem hj')
    rw [ordA_get hj', posA_get h1]
    exact ⟨h1, List.Nodup.idxOf_getElem hnd j hj'⟩
  · rw [posA_get hp] at hpos ⊢
    have hi : ordList.idxOf p < ordList.length := by rw [hl]; exact hpos
    rw [ordA_get hi]
    exact List.getElem_idxOf hi

theorem ordF_val (j : Fin 360) : (ordF j : ℕ) = ordA[j.val]! :=
  Nat.mod_eq_of_lt (ordOK_spec.1 j j.2).1

theorem ordF_mem (j : Fin 360) : ordF j ∈ S0 := by
  show posA[(ordF j : ℕ)]! < 360
  rw [ordF_val, (ordOK_spec.1 j j.2).2]
  exact j.2

theorem posF_ordF (j : Fin 360) : posF (ordF j) = j := by
  apply Fin.ext
  show posA[(ordF j : ℕ)]! % 360 = j
  rw [ordF_val, (ordOK_spec.1 j j.2).2, Nat.mod_eq_of_lt j.2]

theorem posF_val {p : Fin 3510} (hp : p ∈ S0) : (posF p : ℕ) = posA[p.val]! :=
  Nat.mod_eq_of_lt hp

theorem ordF_posF {p : Fin 3510} (hp : p ∈ S0) : ordF (posF p) = p := by
  apply Fin.ext
  rw [ordF_val, posF_val hp]
  exact ordOK_spec.2 p p.2 hp

theorem mem_S0_iff (p : Fin 3510) : p ∈ S0 ↔ (p : ℕ) ∈ ordList := by
  change posA[(p : ℕ)]! < 360 ↔ _
  rw [posA_get p.2, ← d4_facts.1.1, List.idxOf_lt_length_iff]

theorem mem_stabS0_of_maps {g : Equiv.Perm (Fin 3510)}
    (hm : ∀ p : Fin 3510, (p : ℕ) ∈ ordList → ((g p : Fin 3510) : ℕ) ∈ ordList) :
    g ∈ stabS0 := by
  have hmaps' : ∀ p ∈ S0, g p ∈ S0 := fun p hp => by
    rw [mem_S0_iff] at hp ⊢
    exact hm p hp
  have hmaps : ∀ j : Fin 360, g (ordF j) ∈ S0 := fun j => hmaps' _ (ordF_mem j)
  let f : Fin 360 → Fin 360 := fun j => posF (g (ordF j))
  have hf : Function.Injective f := by
    intro i j hij
    have h1 : ordF (posF (g (ordF i))) = ordF (posF (g (ordF j))) := congrArg ordF hij
    rw [ordF_posF (hmaps i), ordF_posF (hmaps j)] at h1
    have h2 := g.injective h1
    rw [← posF_ordF i, ← posF_ordF j, h2]
  have hsurj := Finite.injective_iff_surjective.1 hf
  intro p
  refine ⟨hmaps' p, fun hgp => ?_⟩
  obtain ⟨j, hj⟩ := hsurj (posF (g p))
  have h1 : ordF (posF (g (ordF j))) = ordF (posF (g p)) := congrArg ordF hj
  rw [ordF_posF (hmaps j), ordF_posF hgp] at h1
  rw [← g.injective h1]
  exact ordF_mem j

@[expose] def resFun (g : stabS0) (j : Fin 360) : Fin 360 :=
  posF ((g : Equiv.Perm (Fin 3510)) (ordF j))

theorem resFun_mem (g : stabS0) (j : Fin 360) : (g : Equiv.Perm (Fin 3510)) (ordF j) ∈ S0 :=
  (g.2 (ordF j)).1 (ordF_mem j)

theorem resFun_mul (g h : stabS0) (j : Fin 360) : resFun (g * h) j = resFun g (resFun h j) := by
  unfold resFun
  rw [ordF_posF (resFun_mem h j)]
  rfl

theorem resFun_one (j : Fin 360) : resFun 1 j = j := posF_ordF j

@[expose] def res : stabS0 →* Equiv.Perm (Fin 360) where
  toFun g := ⟨resFun g, resFun g⁻¹, fun j => by rw [← resFun_mul, inv_mul_cancel, resFun_one],
    fun j => by rw [← resFun_mul, mul_inv_cancel, resFun_one]⟩
  map_one' := Equiv.ext resFun_one
  map_mul' g h := Equiv.ext (resFun_mul g h)

theorem res_apply (g : stabS0) (j : Fin 360) : res g j = resFun g j := rfl

theorem ordF_val' (j : Fin 360) : (ordF j : ℕ) = ordList[(j : ℕ)]! := by
  have hj : (j : ℕ) < ordList.length := by rw [d4_facts.1.1]; exact j.2
  rw [ordF_val, ordA_get hj, getElem!_pos ordList (j : ℕ) hj]

theorem res_spec (g : stabS0) (k : Fin 360) (p : Fin 3510) (hp : (p : ℕ) = ordList[(k : ℕ)]!) :
    (((g : Equiv.Perm (Fin 3510)) p : Fin 3510) : ℕ) = ordList[((res g k : Fin 360) : ℕ)]! := by
  have hpk : p = ordF k := Fin.ext (by rw [hp, ordF_val'])
  rw [hpk, ← ordF_val', res_apply, resFun, ordF_posF (resFun_mem g k)]

end S0

section AutModel

@[expose] noncomputable def omegaN : Subgroup ↥autT := omegaT.subgroupOf autT

instance omegaN_normal : omegaN.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [omegaN, Subgroup.mem_subgroupOf] at hn ⊢
  exact (Subgroup.mem_normalizer_iff.1 (autT_le_normalizer g.2) n).1 hn

noncomputable def omegaNEquiv : ↥omegaN ≃* ↥omegaT := Subgroup.subgroupOfEquivOfLe omegaT_le_autT

theorem card_omegaN : Nat.card omegaN = 174182400 := by
  rw [Nat.card_congr omegaNEquiv.toEquiv, card_omegaT]

theorem index_omegaN : omegaN.index = 6 := by
  have h := omegaN.card_mul_index
  rw [card_omegaN, Nat.card_congr (Subgroup.topEquiv (G := ↥autT)).toEquiv.symm] at h
  have h2 : Nat.card ↥(⊤ : Subgroup ↥autT) = 1045094400 := by
    rw [Nat.card_congr (Subgroup.topEquiv (G := ↥autT)).toEquiv, card_autT]
  omega

end AutModel

section AutSimple

open scoped commutatorElement

theorem isSimpleGroup_omegaT : IsSimpleGroup omegaT :=
  CFSG.Timmesfeld.isSimpleGroup_of_lieModel lieModel_omegaT

theorem omegaT_nonabelian : ∃ a b : omegaT, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hc : Subgroup.center omegaT = ⊤ := by
    rw [eq_top_iff]
    intro z _
    exact Subgroup.mem_center_iff.2 fun g => h g z
  rw [center_omegaT] at hc
  have h1 : Nat.card (⊤ : Subgroup omegaT) = 1 := by rw [← hc, Subgroup.card_bot]
  rw [Subgroup.card_top, card_omegaT] at h1
  norm_num at h1

theorem omegaN_perfect : ⁅omegaN, omegaN⁆ = omegaN := by
  haveI : IsSimpleGroup ↥omegaN := @MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_omegaT omegaNEquiv
  have hnab : ∃ a b : ↥omegaN, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := omegaT_nonabelian
    refine ⟨omegaNEquiv.symm a, omegaNEquiv.symm b, fun h => hab ?_⟩
    have := congrArg omegaNEquiv h
    simpa using this
  have htop : commutator ↥omegaN = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥omegaN) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hc : ⁅a, b⁆ ∈ commutator ↥omegaN := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at hc
      exact commutatorElement_eq_one_iff_mul_comm.1 hc
    · exact h
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥omegaN) ⊤ omegaN.subtype
  rw [← commutator_def, htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1.symm

instance isSolvable_autT_quot : Group.IsSolvable (↥autT ⧸ omegaN) := by
  have hcard : Nat.card (↥autT ⧸ omegaN) = 2 ^ 1 * 3 ^ 1 := by
    rw [← Subgroup.index, index_omegaN]
    norm_num
  haveI : Fintype (↥autT ⧸ omegaN) := Fintype.ofFinite _
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)

theorem iInf_derivedSeries_autT : (⨅ n : ℕ, derivedSeries ↥autT n) = omegaN :=
  iInf_derivedSeries_eq omegaN omegaN_perfect

end AutSimple

section General

theorem range_le_of_closure_pair {G H : Type*} [Group G] [Group H] {a b : G}
    (f : ↥(Subgroup.closure ({a, b} : Set G)) →* H) {K : Subgroup H}
    (ha : f ⟨a, Subgroup.subset_closure (Set.mem_insert _ _)⟩ ∈ K)
    (hb : f ⟨b, Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ ∈ K) :
    f.range ≤ K := by
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    rcases hs with rfl | hs
    · exact ha
    · rw [Set.mem_singleton_iff] at hs
      subst hs
      exact hb
  | one =>
    show f 1 ∈ K
    rw [map_one]
    exact K.one_mem
  | mul u v hu hv ihu ihv =>
    show f (⟨u, hu⟩ * ⟨v, hv⟩) ∈ K
    rw [map_mul]
    exact K.mul_mem ihu ihv
  | inv u hu ih =>
    show f (⟨u, hu⟩⁻¹) ∈ K
    rw [map_inv]
    exact K.inv_mem ih

theorem inv_mul_mem_centralizer {G : Type*} [Group G] {m n x : G} (h : m * x * m⁻¹ = n * x * n⁻¹) :
    m⁻¹ * n ∈ Subgroup.centralizer ({x} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc m⁻¹ * n * x = m⁻¹ * (n * x * n⁻¹) * n := by group
    _ = m⁻¹ * (m * x * m⁻¹) * n := by rw [h]
    _ = x * (m⁻¹ * n) := by group

theorem glbCore_map_eq {K L : Type*} [Group K] [Finite K] [Group L] [Finite L] (k : ℕ) (φ : K ≃* L)
    (P : Subgroup K) : (GLBCore 5 k P).map φ.toMonoidHom = GLBCore 5 k (P.map φ.toMonoidHom) := by
  refine le_antisymm (glbCore_map_le (p := 5) (by norm_num) k φ P) ?_
  have h := glbCore_map_le (p := 5) (by norm_num) k φ.symm (P.map φ.toMonoidHom)
  have hP : (P.map φ.toMonoidHom).map φ.symm.toMonoidHom = P := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id P
    ext x
    simp
  rw [hP] at h
  have h2 := Subgroup.map_mono (f := φ.toMonoidHom) h
  have h3 : ((GLBCore 5 k (P.map φ.toMonoidHom)).map φ.symm.toMonoidHom).map φ.toMonoidHom =
      GLBCore 5 k (P.map φ.toMonoidHom) := by
    rw [Subgroup.map_map]
    convert Subgroup.map_id _
    ext x
    simp
  rwa [h3] at h2

end General

section Model

@[expose] noncomputable def stabP : Subgroup fi22P := stabS0.comap fi22P.subtype

theorem mem_stabP_of_rep {t : Array ℕ} (htl : t ∈ [xA, yA, hA, n1A, n2A, zA]) {g : fi22P}
    (ht : Rep 3510 t g.1) : g ∈ stabP :=
  mem_stabS0_of_maps (d4_facts.2.1 t htl _ ht)

theorem stabP_ne_top : stabP ≠ ⊤ := by
  intro h
  obtain ⟨A, hAP, hA⟩ := exists_rep_evalW (w := [1]) (by decide)
  have hmem : (⟨A, hAP⟩ : fi22P) ∈ stabP := h ▸ Subgroup.mem_top _
  have hmem' : A ∈ stabS0 := hmem
  obtain ⟨p, hp, hout⟩ := d4_facts.2.2.1 A hA
  exact hout ((mem_S0_iff _).1 ((hmem' p).1 ((mem_S0_iff p).2 hp)))

theorem orbit_part' : ∃ x y n₁ n₂ : fi22P, Rep 3510 xA x.1 ∧ Rep 3510 yA y.1 ∧ Rep 3510 n1A n₁.1 ∧
    Rep 3510 n2A n₂.1 ∧ PlaneData x y ∧
    n₁ ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set fi22P) : Subgroup fi22P) : Set fi22P) ∧
    n₂ ∈ Subgroup.normalizer ((Subgroup.closure ({x, y} : Set fi22P) : Subgroup fi22P) : Set fi22P) ∧
    ∀ v : Fin 2 → ZMod 5, v ≠ 0 → ∃ w : List ℕ,
      wordProdN n₁ n₂ w * x * (wordProdN n₁ n₂ w)⁻¹ = planeMap x y v := by
  have h := orb_check
  unfold orbCheck at h
  simp only [Bool.and_eq_true, and_assoc] at h
  obtain ⟨hlx, hly, hl1, hl2, hx5, hy5, hcomm, hne, c1x, c1y, c2x, c2y, hconj⟩ := h
  obtain ⟨X, hXP, hX⟩ := exists_rep_evalW hlx
  obtain ⟨Y, hYP, hY⟩ := exists_rep_evalW hly
  obtain ⟨N1, hN1P, hN1⟩ := exists_rep_evalW hl1
  obtain ⟨N2, hN2P, hN2⟩ := exists_rep_evalW hl2
  have hX' : Rep 3510 xA X := hX
  have hY' : Rep 3510 yA Y := hY
  have hN1' : Rep 3510 n1A N1 := hN1
  have hN2' : Rep 3510 n2A N2 := hN2
  have hX5 : X ^ 5 = 1 := (eqA_iff (rep_pw hX' 5) rep_idA).1 hx5
  have hY5 : Y ^ 5 = 1 := (eqA_iff (rep_pw hY' 5) rep_idA).1 hy5
  have hXY : X * Y = Y * X := (eqA_iff (rep_compA hX' hY') (rep_compA hY' hX')).1 hcomm
  have hne' : ∀ i < 5, ∀ j < 5, ¬ (i = 0 ∧ j = 0) → X ^ i * Y ^ j ≠ 1 := by
    intro i hi j hj hij h1
    have h2 := allLt_spec (allLt_spec hne hi) hj
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h2
    rcases h2 with h2 | h2
    · exact hij h2
    · have := (eqA_iff (rep_planeA hX' hY' i j) rep_idA).2 h1
      rw [this] at h2
      exact Bool.noConfusion h2
  have hN1X : N1 * X = X ^ 2 * Y ^ 3 * N1 :=
    (eqA_iff (rep_compA hN1' hX') (rep_compA (rep_planeA hX' hY' 2 3) hN1')).1 c1x
  have hN1Y : N1 * Y = X ^ 1 * Y ^ 2 * N1 :=
    (eqA_iff (rep_compA hN1' hY') (rep_compA (rep_planeA hX' hY' 1 2) hN1')).1 c1y
  have hN2X : N2 * X = X ^ 4 * Y ^ 1 * N2 :=
    (eqA_iff (rep_compA hN2' hX') (rep_compA (rep_planeA hX' hY' 4 1) hN2')).1 c2x
  have hN2Y : N2 * Y = X ^ 1 * Y ^ 1 * N2 :=
    (eqA_iff (rep_compA hN2' hY') (rep_compA (rep_planeA hX' hY' 1 1) hN2')).1 c2y
  set x : fi22P := ⟨X, hXP⟩ with hx_def
  set y : fi22P := ⟨Y, hYP⟩ with hy_def
  set n1 : fi22P := ⟨N1, hN1P⟩ with hn1_def
  set n2 : fi22P := ⟨N2, hN2P⟩ with hn2_def
  have hD : PlaneData x y := by
    refine ⟨Subtype.ext hX5, Subtype.ext hY5, Subtype.ext hXY, fun v hv h => ?_⟩
    refine hne' (v 0).val (ZMod.val_lt _) (v 1).val (ZMod.val_lt _) ?_ (congrArg Subtype.val h)
    rintro ⟨h0, h1⟩
    exact hv (funext fun i => by
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1)
  have hxm : ∀ i j : ℕ, x ^ i * y ^ j ∈ Subgroup.closure ({x, y} : Set fi22P) := fun i j =>
    Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
  have hconj_of : ∀ (n a b : fi22P), n * a = b * n → n * a * n⁻¹ = b := fun n a b h => by
    rw [h]
    group
  have hn1x : n1 * x * n1⁻¹ = x ^ 2 * y ^ 3 := hconj_of _ _ _ (Subtype.ext hN1X)
  have hn1y : n1 * y * n1⁻¹ = x ^ 1 * y ^ 2 := hconj_of _ _ _ (Subtype.ext hN1Y)
  have hn2x : n2 * x * n2⁻¹ = x ^ 4 * y ^ 1 := hconj_of _ _ _ (Subtype.ext hN2X)
  have hn2y : n2 * y * n2⁻¹ = x ^ 1 * y ^ 1 := hconj_of _ _ _ (Subtype.ext hN2Y)
  have hn1 := mem_normalizer_closure_pair (x := x) (y := y) (n := n1)
    (by rw [hn1x]; exact hxm 2 3) (by rw [hn1y]; exact hxm 1 2)
  have hn2 := mem_normalizer_closure_pair (x := x) (y := y) (n := n2)
    (by rw [hn2x]; exact hxm 4 1) (by rw [hn2y]; exact hxm 1 1)
  refine ⟨x, y, n1, n2, hX', hY', hN1', hN2', hD, hn1, hn2, fun v hv => ?_⟩
  have hspec := allLt_spec (allLt_spec hconj (ZMod.val_lt (v 0))) (ZMod.val_lt (v 1))
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.any_eq_true] at hspec
  rcases hspec with ⟨h0, h1⟩ | ⟨t, ht, ⟨hti, htj⟩, htok⟩
  · exact absurd (funext fun i => by
      fin_cases i
      · exact (ZMod.val_eq_zero _).1 h0
      · exact (ZMod.val_eq_zero _).1 h1) hv
  · refine ⟨t.2.2, ?_⟩
    have hM := rep_nProd hN1' hN2' t.2.2
    have hrel : wordProdN N1 N2 t.2.2 * X =
        (X ^ (v 0).val * Y ^ (v 1).val) * wordProdN N1 N2 t.2.2 := by
      have := (eqA_iff (rep_compA hM hX') (rep_compA (rep_planeA hX' hY' t.1 t.2.1) hM)).1 htok
      rwa [hti, htj] at this
    have hcoe : (wordProdN n1 n2 t.2.2).1 = wordProdN N1 N2 t.2.2 :=
      wordProdN_map fi22P.subtype n1 n2 t.2.2
    apply Subtype.ext
    show (wordProdN n1 n2 t.2.2).1 * X * ((wordProdN n1 n2 t.2.2).1)⁻¹ =
      X ^ (v 0).val * Y ^ (v 1).val
    rw [hcoe, mul_inv_eq_iff_eq_mul]
    exact hrel

theorem model_main : ∃ (x y : fi22P) (Γ : Subgroup fi22P), PlaneData x y ∧
    GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) = Γ ∧ Nonempty (↥Γ ≃* ↥autT) := by
  obtain ⟨x, y, n₁, n₂, hx, hy, hn₁, hn₂, hD, hn₁N, hn₂N, hconjW⟩ := orbit_part'
  have hN : NormData x y := fun v hv => by
    obtain ⟨w, hw⟩ := hconjW v hv
    exact ⟨wordProdN n₁ n₂ w, wordProdN_mem hn₁N hn₂N w, hw⟩
  have hS : Star5Data x y := star5_part hx hy hD
  obtain ⟨G₁, G₂, h₁, h₂, hG₁, hG₂⟩ := gen_part hx hy hD
  have hΓle : Subgroup.closure ({G₁, G₂} : Set fi22P) ≤
      GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    exacts [hG₁, hG₂]
  have hmax := closure_maximal h₁ h₂
  obtain ⟨Z, hZ, hZx⟩ := z_gen hx
  have hZS : Z ∈ stabP := mem_stabP_of_rep (by simp) hZ
  have hn₁S : n₁ ∈ stabP := mem_stabP_of_rep (by simp) hn₁
  have hn₂S : n₂ ∈ stabP := mem_stabP_of_rep (by simp) hn₂
  obtain ⟨H, hH, L, hLeq, -, hCL, -⟩ := centralizer_closure_facts hx hy hD
  have hLS : L ≤ stabS0 := by
    rw [hLeq, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact mem_stabS0_of_maps (d4_facts.2.1 xA (by simp) _ hx)
    · exact mem_stabS0_of_maps (d4_facts.2.1 yA (by simp) _ hy)
    · exact mem_stabS0_of_maps (d4_facts.2.1 hA (by simp) _ hH)
  have hCS : ∀ c : fi22P, c ∈ Subgroup.centralizer ({x} : Set fi22P) → c ∈ stabP :=
    fun c hc => hLS (hCL c hc)
  have hx5 : x ^ 5 = 1 := hD.x_pow
  have hx1 : x ≠ 1 := hD.x_ne_one
  have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hZpow : ∀ a : ℕ, Z ^ a * x * (Z ^ a)⁻¹ = x ^ (2 ^ a) := by
    intro a
    induction a with
    | zero => simp
    | succ a ih =>
      have hZx' : Z * x * Z⁻¹ = x ^ 2 := by rw [hZx]; group
      calc Z ^ (a + 1) * x * (Z ^ (a + 1))⁻¹ = Z * (Z ^ a * x * (Z ^ a)⁻¹) * Z⁻¹ := by group
        _ = Z * x ^ (2 ^ a) * Z⁻¹ := by rw [ih]
        _ = (Z * x * Z⁻¹) ^ (2 ^ a) := by rw [conj_pow]
        _ = x ^ (2 ^ (a + 1)) := by rw [hZx', ← pow_mul]; congr 1; ring
  have hNx : ∀ n : fi22P,
      n ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup fi22P) : Set fi22P) → n ∈ stabP := by
    intro n hn
    have hxn : n * x * n⁻¹ ∈ Subgroup.zpowers x :=
      (Subgroup.mem_normalizer_iff.1 hn x).1 (Subgroup.mem_zpowers x)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxn
    obtain ⟨r, hr5, hxr⟩ : ∃ r : ℕ, r < 5 ∧ x ^ r = n * x * n⁻¹ := by
      refine ⟨(k % 5).toNat, by omega, ?_⟩
      have h1 : ((k % 5).toNat : ℤ) = k % 5 := Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
      rw [← zpow_natCast, h1, ← hk]
      have := zpow_mod_orderOf x k
      rw [hord] at this
      exact_mod_cast this
    have key : ∃ a : ℕ, Z ^ a * x * (Z ^ a)⁻¹ = n * x * n⁻¹ := by
      rw [← hxr]
      interval_cases r
      · exfalso
        apply hx1
        rw [pow_zero] at hxr
        have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [e, ← hxr]
        group
      · exact ⟨0, by simp⟩
      · exact ⟨1, by rw [hZpow]; norm_num⟩
      · refine ⟨3, ?_⟩
        rw [hZpow, show 2 ^ 3 = 5 + 3 by norm_num, pow_add, hx5, one_mul]
      · exact ⟨2, by rw [hZpow]; norm_num⟩
    obtain ⟨a, ha⟩ := key
    have hc := inv_mul_mem_centralizer ha
    have e : n = Z ^ a * ((Z ^ a)⁻¹ * n) := by group
    rw [e]
    exact stabP.mul_mem (stabP.pow_mem hZS a) (hCS _ hc)
  have hconjS : ∀ v : Fin 2 → ZMod 5, v ≠ 0 → ∃ m ∈ stabP, m * x * m⁻¹ = planeMap x y v := by
    intro v hv
    obtain ⟨w, hw⟩ := hconjW v hv
    exact ⟨wordProdN n₁ n₂ w, wordProdN_mem hn₁S hn₂S w, hw⟩
  obtain ⟨hTel, hTc, hTpl⟩ := hD.closure_facts
  have hpl1 : ∀ v : Fin 2 → ZMod 5, planeMap x y v ≠ 1 → v ≠ 0 := by
    rintro v hv rfl
    exact hv (by simp [planeMap])
  have hcore : GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) ≤ stabP := by
    refine sSup_le ?_
    rintro _ ⟨Q, hQT, hQk, rfl⟩
    obtain ⟨E, hEQ, -, hEc⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 5) Q
    have hQ5 : 5 ≤ Nat.card Q := by
      calc 5 = 5 ^ 1 := by norm_num
        _ ≤ 5 ^ CFSG.Open.pRank 5 Q := Nat.pow_le_pow_right (by norm_num) hQk
        _ = Nat.card E := hEc.symm
        _ ≤ Nat.card Q := Subgroup.card_le_of_le hEQ
    have hdvd : Nat.card Q ∣ 5 ^ 2 := hTc ▸ Subgroup.card_dvd_of_le hQT
    obtain ⟨i, hi2, hQi⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hdvd
    have hi1 : 1 ≤ i := by
      by_contra hi0
      have : i = 0 := by omega
      rw [this, pow_zero] at hQi
      omega
    interval_cases i
    ·
      obtain ⟨t, htQ, ht1⟩ : ∃ t ∈ Q, t ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have hQb : Q = ⊥ := (Subgroup.eq_bot_iff_forall Q).2 hcon
        rw [hQb, Subgroup.card_bot] at hQi
        norm_num at hQi
      obtain ⟨v, rfl⟩ := hTpl t (hQT htQ)
      obtain ⟨m, hmS, hm⟩ := hconjS v (hpl1 v ht1)
      have ht5 : planeMap x y v ^ 5 = 1 := hTel.2 _ (hQT htQ)
      have htord : orderOf (planeMap x y v) = 5 := orderOf_eq_prime ht5 ht1
      have hQt : Q = Subgroup.zpowers (planeMap x y v) :=
        (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 htQ)
          (by rw [hQi, Nat.card_zpowers, htord, pow_one])).symm
      have hzm : (Subgroup.zpowers x).map (MulAut.conj m).toMonoidHom =
          Subgroup.zpowers (planeMap x y v) := by
        rw [MonoidHom.map_zpowers, ← hm]
        rfl
      rw [hQt, ← hzm, ← Subgroup.map_equiv_normalizer_eq]
      rintro _ ⟨n', hn', rfl⟩
      show m * n' * m⁻¹ ∈ stabP
      exact stabP.mul_mem (stabP.mul_mem hmS (hNx n' hn')) (stabP.inv_mem hmS)
    ·
      have hQT' : Q = Subgroup.closure ({x, y} : Set fi22P) :=
        Subgroup.eq_of_le_of_card_ge hQT (by rw [hQi, hTc])
      rw [hQT']
      intro n hn
      have hxT : x ∈ Subgroup.closure ({x, y} : Set fi22P) := Subgroup.subset_closure (by simp)
      have hnx : n * x * n⁻¹ ∈ Subgroup.closure ({x, y} : Set fi22P) :=
        (Subgroup.mem_normalizer_iff.1 hn x).1 hxT
      obtain ⟨v, hv⟩ := hTpl _ hnx
      have hne : n * x * n⁻¹ ≠ 1 := by
        intro h1
        apply hx1
        have e : x = n⁻¹ * (n * x * n⁻¹) * n := by group
        rw [e, h1]
        group
      obtain ⟨m, hmS, hm⟩ := hconjS v (hpl1 v (hv ▸ hne))
      have hc := inv_mul_mem_centralizer (hm.trans hv.symm)
      have e : n = m * (m⁻¹ * n) := by group
      rw [e]
      exact stabP.mul_mem hmS (hCS _ hc)
  have hΓeq : GLBCore 5 1 (Subgroup.closure ({x, y} : Set fi22P)) =
      Subgroup.closure ({G₁, G₂} : Set fi22P) := by
    rcases hmax _ hΓle with h | h
    · exact h
    · exfalso
      rw [h, top_le_iff] at hcore
      exact stabP_ne_top hcore
  refine ⟨x, y, Subgroup.closure ({G₁, G₂} : Set fi22P), hD, hΓeq, ?_⟩
  set Γ := Subgroup.closure ({G₁, G₂} : Set fi22P) with hΓdef
  have hΓS : Γ ≤ stabP := hΓeq ▸ hcore
  let ψ : ↥Γ →* ↥stabS0 :=
    MonoidHom.codRestrict (fi22P.subtype.comp Γ.subtype) stabS0 (fun γ => hΓS γ.2)
  let ρ : ↥Γ →* Equiv.Perm (Fin 360) := res.comp ψ
  have hG₁Γ : G₁ ∈ Γ := Subgroup.subset_closure (Set.mem_insert _ _)
  have hG₂Γ : G₂ ∈ Γ := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hrange : ρ.range ≤ autT :=
    range_le_of_closure_pair ρ
      (d4_facts.2.2.2.1 g1A (by simp) _ h₁ _ fun k p hp => res_spec (ψ ⟨G₁, hG₁Γ⟩) k p hp)
      (d4_facts.2.2.2.1 g2A (by simp) _ h₂ _ fun k p hp => res_spec (ψ ⟨G₂, hG₂Γ⟩) k p hp)
  have hTΓ : Subgroup.closure ({x, y} : Set fi22P) ≤ Γ :=
    hΓeq ▸ (Subgroup.le_normalizer.trans hD.normalizer_le)
  have hfaith : ∀ (t : fi22P) (ht : t ∈ Subgroup.closure ({x, y} : Set fi22P)),
      ρ ⟨t, hTΓ ht⟩ = 1 → t = 1 := by
    intro t ht h1
    obtain ⟨v, rfl⟩ := hTpl t ht
    by_contra hne
    have h1' : res (ψ ⟨planeMap x y v, hTΓ ht⟩) = 1 := h1
    have hfix : ∀ p : Fin 3510, (p : ℕ) ∈ ordList →
        ((planeMap x y v).1 : Equiv.Perm (Fin 3510)) p = p := by
      intro p hp
      have hpS : p ∈ S0 := (mem_S0_iff p).2 hp
      have e := res_spec (ψ ⟨planeMap x y v, hTΓ ht⟩) (posF p) p (by rw [← ordF_val', ordF_posF hpS])
      rw [h1', Equiv.Perm.one_apply, ← ordF_val', ordF_posF hpS] at e
      exact Fin.ext e
    have hij : (v 0).val ≠ 0 ∨ (v 1).val ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hne (by simp [planeMap, hc.1, hc.2])
    obtain ⟨p, hp, hmove⟩ :=
      d4_facts.2.2.2.2 x.1 y.1 hx hy _ _ (ZMod.val_lt (v 0)) (ZMod.val_lt (v 1)) hij
    apply hmove
    have h2 := hfix p hp
    simpa [planeMap] using h2
  let f : ↥(Subgroup.closure ({x, y} : Set fi22P)) →* Equiv.Perm (Fin 360) :=
    ρ.comp (Subgroup.inclusion hTΓ)
  have hfinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro t ht
    exact Subtype.ext (hfaith t.1 t.2 ht)
  have h25 : 5 ^ 2 ∣ Nat.card ρ.range := by
    have hle : f.range ≤ ρ.range := by
      rintro _ ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    have hcf : Nat.card f.range = 5 ^ 2 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hTc]
    rw [← hcf]
    exact Subgroup.card_dvd_of_le hle
  have hsplit : Nat.card Γ = Nat.card ρ.range * Nat.card ρ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  have hΓdvd : Nat.card Γ ∣ 5 ^ 2 * 2582470066176 := by
    have := Subgroup.card_subgroup_dvd_card Γ
    rwa [card_fi22P] at this
  have hker5 : ¬ 5 ∣ Nat.card ρ.ker := by
    intro h5
    obtain ⟨r, hr⟩ := h25
    obtain ⟨s, hs⟩ := h5
    rw [hsplit, hr, hs] at hΓdvd
    have h1 : 5 ^ 2 * (5 * (r * s)) ∣ 5 ^ 2 * 2582470066176 := by
      have e : 5 ^ 2 * r * (5 * s) = 5 ^ 2 * (5 * (r * s)) := by ring
      rwa [e] at hΓdvd
    have h2 : 5 * (r * s) ∣ 2582470066176 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
    have h3 : 5 ∣ 2582470066176 := (Dvd.intro _ rfl).trans h2
    norm_num at h3
  set K : Subgroup fi22P := ρ.ker.map Γ.subtype with hKdef
  have hKc : Nat.card K = Nat.card ρ.ker := Subgroup.card_map_of_injective Γ.subtype_injective
  have hKN : Subgroup.closure ({x, y} : Set fi22P) ≤ Subgroup.normalizer (K : Set fi22P) := by
    intro t ht
    refine Subgroup.mem_normalizer_fintype fun k hk => ?_
    obtain ⟨κ, hκ, rfl⟩ := hk
    have hκ' : (⟨t, hTΓ ht⟩ : ↥Γ) * κ * (⟨t, hTΓ ht⟩ : ↥Γ)⁻¹ ∈ ρ.ker :=
      (MonoidHom.normal_ker ρ).conj_mem κ hκ _
    exact ⟨_, hκ', rfl⟩
  have hK : K = ⊥ := coprime_core hD hN hS K (by rw [hKc]; exact hker5) hKN
  have hkerbot : ρ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro κ hκ
    have : (κ : fi22P) ∈ K := ⟨κ, hκ, rfl⟩
    rw [hK, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  have hρinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hkerbot
  have hΓcard : 1045094400 ≤ Nat.card Γ := by
    have h1 := card_closure_ge h₁ h₂
    have h2 : Γ.map fi22P.subtype =
        Subgroup.closure ({G₁.1, G₂.1} : Set (Equiv.Perm (Fin 3510))) := by
      rw [hΓdef, MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← h2, Subgroup.card_map_of_injective fi22P.subtype_injective] at h1
    exact h1
  have hrange_eq : ρ.range = autT := by
    refine Subgroup.eq_of_le_of_card_ge hrange ?_
    rw [card_autT, ← Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv]
    exact hΓcard
  exact ⟨(MonoidHom.ofInjective hρinj).trans (MulEquiv.subgroupCongr hrange_eq)⟩

end Model

section Main

theorem lieModelM_omegaT :
    CFSG.Models.LieModel omegaT .POmegaPlus 4 2 1 :=
  ⟨statedClassicalModel_omegaT.1, Or.inl statedClassicalModel_omegaT⟩

theorem inputGammaD4_holds : Claims1110f.InputGammaD4 := by
  intro X _ _ hX P hPp hPc
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨-, hf5, h25, -⟩ := CFSG.HardMathSupport.Solomon.Proving.fi22Facts_holds X hX
  have hPc' : Nat.card P = 5 ^ (Nat.card X).factorization 5 := by rw [hPc, hf5]
  have hPsyl : IsSylowIn 5 ⊤ P :=
    Claims1110.isSylowIn_of_card le_top hPp (by rw [Subgroup.card_top]; exact hPc')
  have hord : ∀ x ∈ P, x ≠ 1 → orderOf x = 5 := by
    intro x hxP hx1
    have hd : orderOf x ∣ 5 ^ 2 := hPc ▸ Subgroup.orderOf_dvd_natCard P hxP
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).1 hd
    interval_cases j
    · rw [pow_zero, orderOf_eq_one_iff] at hjx
      exact absurd hjx hx1
    · rw [hjx, pow_one]
    · exact absurd hjx (h25 x)
  have hlay : ∀ x ∈ P, x ≠ 1 →
      Subgroup.center ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) = ⊥ ∧
        5 ∣ Nat.card ↥(GLAPLayer 5 (Subgroup.centralizer ({x} : Set X))) := by
    intro x hxP hx1
    obtain ⟨ψ⟩ := SporFacts.input14_21_holds X hX x (hord x hxP hx1)
    refine ⟨Claims1110e.center_eq_bot_of_isAltType_five ⟨ψ⟩, ?_⟩
    rw [Nat.card_congr ψ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hγ := Claims1110f.gammaK0_eq_glbCore hPc hPsyl hord hlay
  obtain ⟨φ₀⟩ := hX
  obtain ⟨β⟩ := CFSG.Sporadic.Bridge.Fi22.nonempty_mulEquiv
  let φ : X ≃* fi22P := (φ₀.trans β.symm).trans fi22PermEquiv
  obtain ⟨x, y, Γ, hD, hΓ, ⟨θ⟩⟩ := model_main
  have hcardP : Nat.card fi22P = 5 ^ 2 * 2582470066176 := by rw [card_fi22P]; norm_num
  have hm5 : ¬ 5 ∣ 2582470066176 := by norm_num
  have hf : (Nat.card fi22P).factorization 5 = 2 := by
    rw [hcardP, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hm5, add_zero, Nat.Prime.factorization_pow (by norm_num)]
    simp
  have hP'c : Nat.card (P.map φ.toMonoidHom) = 5 ^ (Nat.card fi22P).factorization 5 := by
    rw [Subgroup.card_map_of_injective φ.injective, hPc, hf]
  obtain ⟨g, hg⟩ := hD.exists_conj_closure hcardP hm5 (Sylow.ofCard _ hP'c)
  have hT : (Subgroup.closure ({x, y} : Set fi22P)).map (MulAut.conj g).toMonoidHom =
      P.map φ.toMonoidHom := by
    rw [← closure_pair_map x y (MulAut.conj g)]
    simp only [MulAut.conj_apply]
    rw [hg, Sylow.coe_ofCard]
  set ψ : X ≃* fi22P := φ.trans (MulAut.conj g).symm with hψdef
  have hψ : (Claims1110b.gammaK0 P).map ψ.toMonoidHom = Γ := by
    have h1 : (GLBCore 5 1 P).map φ.toMonoidHom = Γ.map (MulAut.conj g).toMonoidHom := by
      rw [glbCore_map_eq 1 φ P, ← hT, ← glbCore_map_eq 1 (MulAut.conj g), hΓ]
    have h2 : ψ.toMonoidHom = (MulAut.conj g).symm.toMonoidHom.comp φ.toMonoidHom := rfl
    rw [hγ, h2, ← Subgroup.map_map, h1, Subgroup.map_map]
    convert Subgroup.map_id Γ
    ext z
    simp
  set H := Claims1110b.gammaK0 P with hHdef
  let θ' : ↥H ≃* ↥autT :=
    ((Subgroup.equivMapOfInjective H ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hψ)).trans θ
  have hder : derivedInf H = (omegaN.comap θ'.toMonoidHom).map H.subtype := by
    rw [derivedInf_eq_of_mulEquiv H θ', iInf_derivedSeries_autT]
  set S : Subgroup ↥H := omegaN.comap θ'.toMonoidHom with hSdef
  have hSmap : S = omegaN.map θ'.symm.toMonoidHom := Subgroup.comap_equiv_eq_map_symm' θ' omegaN
  let e : ↥(derivedInf H) ≃* ↥omegaT :=
    (MulEquiv.subgroupCongr hder).trans
      ((Subgroup.equivMapOfInjective S H.subtype H.subtype_injective).symm.trans
        ((MulEquiv.subgroupCongr hSmap).trans ((θ'.symm.subgroupMap omegaN).symm.trans omegaNEquiv)))
  refine ⟨@MulEquiv.isSimpleGroup _ _ _ _ isSimpleGroup_omegaT e, ?_,
    CFSG.Models.LieModel.of_mulEquiv e.symm lieModelM_omegaT, ?_⟩
  · obtain ⟨a, b, hab⟩ := omegaT_nonabelian
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have := congrArg e h
    simpa using this
  ·
    have hPH : P ≤ H := by
      rw [hHdef]
      unfold Claims1110b.gammaK0
      exact Subgroup.le_normalizer.trans le_sup_left
    intro p hp
    rw [hder]
    refine ⟨⟨p, hPH hp⟩, ?_, rfl⟩
    have hp25 : (⟨p, hPH hp⟩ : ↥H) ^ 25 = 1 := by
      have h1 : (⟨p, hp⟩ : ↥P) ^ Nat.card P = 1 := pow_card_eq_one'
      rw [hPc] at h1
      exact Subtype.ext (by simpa using congrArg Subtype.val h1)
    have hq : (θ'.toMonoidHom ⟨p, hPH hp⟩) ^ 25 = 1 := by rw [← map_pow, hp25, map_one]
    exact Sec13d.mem_of_index_coprime omegaN hq (by rw [index_omegaN]; norm_num)

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110g
