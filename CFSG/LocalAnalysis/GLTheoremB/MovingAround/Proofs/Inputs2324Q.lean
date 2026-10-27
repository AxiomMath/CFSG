module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs123b
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ThreeKill
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM12
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenM22
public import Certificates.Certificate232401
public import Certificates.Certificate232402
public import Certificates.Certificate232403

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.RankThree.PartTwo.Sec4.Item434SporGen (NoSignalizer)

section Gen

@[expose] def GenPlane {X : Type} [Group X] (P : Subgroup X) : Prop :=
  (⊤ : Subgroup X) ≤ ⨆ (x : X) (_ : x ∈ P) (_ : x ≠ 1), pCoreOf 2 (Subgroup.centralizer {x})

@[expose] def GenAut {X : Type} [Group X] (B : Subgroup (MulAut X)) : Prop :=
  (⊤ : Subgroup X) ≤ ⨆ (β : MulAut X) (_ : β ∈ B) (_ : β ≠ 1), pCoreOf 2 (fixSub β)

theorem map_pCoreOf_le {X X' : Type*} [Group X] [Group X'] [Finite X] (f : X ≃* X')
    (H : Subgroup X) : (pCoreOf 2 H).map f.toMonoidHom ≤ pCoreOf 2 (H.map f.toMonoidHom) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (Subgroup.map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 H)) ?_
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).map f.toMonoidHom)
  rintro _ ⟨h, hh, rfl⟩
  exact Subgroup.le_normalizer_map f.toMonoidHom
    (Subgroup.mem_map_of_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hh))

theorem map_centralizer_singleton {X X' : Type*} [Group X] [Group X'] (f : X ≃* X') (x : X) :
    (Subgroup.centralizer ({x} : Set X)).map f.toMonoidHom = Subgroup.centralizer {f x} := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [← map_mul, ← map_mul, hz]
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    apply f.injective
    rw [map_mul, map_mul, f.apply_symm_apply, hy]

theorem GenPlane.of_map {X X' : Type} [Group X] [Group X'] [Finite X'] (f : X ≃* X')
    {P : Subgroup X} (h : GenPlane (P.map f.toMonoidHom)) : GenPlane P := by
  have key : (⨆ (x' : X') (_ : x' ∈ P.map f.toMonoidHom) (_ : x' ≠ 1),
      pCoreOf 2 (Subgroup.centralizer {x'})).map f.symm.toMonoidHom ≤
      ⨆ (x : X) (_ : x ∈ P) (_ : x ≠ 1), pCoreOf 2 (Subgroup.centralizer {x}) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun x' => iSup_le fun hx' => iSup_le fun hx'1 => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    obtain ⟨x, hx, rfl⟩ := hx'
    have hx1 : x ≠ 1 := fun h1 => hx'1 (by rw [h1, map_one])
    refine (map_pCoreOf_le f.symm _).trans ?_
    rw [map_centralizer_singleton]
    refine le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le hx1 ?_))
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, le_refl]
  intro g _
  exact key ⟨f g, h (Subgroup.mem_top _), f.symm_apply_apply g⟩

theorem GenPlane.map {X X' : Type} [Group X] [Group X'] [Finite X] (f : X ≃* X')
    {P : Subgroup X} (h : GenPlane P) : GenPlane (P.map f.toMonoidHom) := by
  refine GenPlane.of_map f.symm ?_
  have e : (P.map f.toMonoidHom).map f.symm.toMonoidHom = P := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, f.symm_apply_apply x⟩
  rw [e]
  exact h

theorem fixSub_conj {X : Type} [Group X] (x : X) :
    fixSub (MulAut.conj x) = Subgroup.centralizer {x} := by
  ext y
  change (MulAut.conj x) y = y ↔ y ∈ Subgroup.centralizer {x}
  rw [Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply]
  constructor
  · intro h
    calc y * x = x * y * x⁻¹ * x := by rw [h]
      _ = x * y := by group
  · intro h
    rw [← h]
    group

theorem genAut_of_genPlane {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) {P : Subgroup X}
    (h : GenPlane P) : GenAut (P.map (MulAut.conj : X →* MulAut X)) := by
  have hinj := CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hZ
  refine h.trans (iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_)
  refine le_iSup_of_le (MulAut.conj x) (le_iSup_of_le (Subgroup.mem_map_of_mem _ hx)
    (le_iSup_of_le (fun h1 => hx1 (hinj (h1.trans (map_one _).symm))) ?_))
  rw [fixSub_conj]

theorem pCoreOf_two_le {G : Type*} [Group G] [Finite G] (H : Subgroup G) :
    pCoreOf 2 H ≤ GLAPPrimeCoreOf 3 H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine Subgroup.map_mono ?_
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).exists_card_eq
  refine CFSG.le_pPrimeCore_of_normal_coprime CFSG.pCore_normal ?_
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

end Gen

section Lift

variable {Y : Type} [Group Y] [Finite Y]

theorem top_le_of_genAut (hperf : commutator Y = ⊤) (hZ : IsPGroup 3 ↥(Subgroup.center Y))
    {A : Subgroup (MulAut Y)} (h : GenAut (A.map (quotientCenterAut' Y))) :
    (⊤ : Subgroup Y) ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1), GLAPPrimeCoreOf 3 (fixSub α) := by
  set M : Subgroup Y := ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1), pCoreOf 2 (fixSub α) with hM
  have hMle : M ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1), GLAPPrimeCoreOf 3 (fixSub α) :=
    iSup_mono fun _ => iSup_mono fun _ => iSup_mono fun _ => pCoreOf_two_le _
  have hMtop : M.map (QuotientGroup.mk' (Subgroup.center Y)) = ⊤ := by
    refine eq_top_iff.2 (h.trans (iSup_le fun β => iSup_le fun hβ => iSup_le fun hβ1 => ?_))
    obtain ⟨α, hα, rfl⟩ := hβ
    have hα1 : α ≠ 1 := fun h1 => hβ1 (by rw [h1, map_one])
    intro w hw
    obtain ⟨y, hy, hyw⟩ := AltFacts2.exists_mem_pCoreOf_lift hZ α hw
    have hle : pCoreOf 2 (fixSub α) ≤ M :=
      le_iSup_of_le α (le_iSup_of_le hα (le_iSup_of_le hα1 le_rfl))
    exact ⟨y, hle hy, hyw⟩
  rw [← AltFacts2.eq_top_of_map_center_eq_top hperf hMtop]
  exact hMle

theorem noSig_of_quot (hperf : commutator Y = ⊤) {A : Subgroup (MulAut Y)}
    (h : ∀ W : Subgroup (MulAut (Y ⧸ Subgroup.center Y)), ¬ 3 ∣ Nat.card W →
      A.map (quotientCenterAut' Y) ≤
        Subgroup.normalizer (W : Set (MulAut (Y ⧸ Subgroup.center Y))) → W = ⊥) :
    ∀ W : Subgroup (MulAut Y), ¬ 3 ∣ Nat.card W →
      A ≤ Subgroup.normalizer (W : Set (MulAut Y)) → W = ⊥ := by
  intro W hW hAW
  have hinj := quotientCenterAut'_injective hperf
  have h1 := h (W.map (quotientCenterAut' Y)) (by rwa [Subgroup.card_map_of_injective hinj]) (by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.le_normalizer_map _ (Subgroup.mem_map_of_mem _ (hAW ha)))
  exact (Subgroup.map_eq_bot_iff_of_injective _ hinj).1 h1

end Lift

section Balance

theorem mem_normalizer_of_map_le {G : Type*} [Group G] {T : Subgroup G} {a : G}
    (h1 : T.map (MulAut.conj a).toMonoidHom ≤ T) (h2 : T.map (MulAut.conj a⁻¹).toMonoidHom ≤ T) :
    a ∈ Subgroup.normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · intro hn
    exact h1 ⟨n, hn, rfl⟩
  · intro hn
    have e : (MulAut.conj a⁻¹).toMonoidHom (a * n * a⁻¹) = n := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [← e]
    exact h2 ⟨_, hn, rfl⟩

theorem map_conj_eq_of_mem_normalizer {G : Type*} [Group G] {L : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) : L.map (MulAut.conj b).toMonoidHom = L := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hb y).1 hy
  · intro hx
    have e : b * (b⁻¹ * x * b) * b⁻¹ = x := by group
    refine ⟨b⁻¹ * x * b, (Subgroup.mem_normalizer_iff.1 hb _).2 (by rw [e]; exact hx), ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, e]

theorem normalizer_le_normalizer_pCoreOf {G : Type*} [Group G] [Finite G] (L : Subgroup G) :
    Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
  intro a ha
  refine mem_normalizer_of_map_le ?_ ?_
  · calc (pCoreOf 2 L).map (MulAut.conj a).toMonoidHom
          ≤ pCoreOf 2 (L.map (MulAut.conj a).toMonoidHom) := map_pCoreOf_le (MulAut.conj a) L
      _ = pCoreOf 2 L := by rw [map_conj_eq_of_mem_normalizer ha]
  · calc (pCoreOf 2 L).map (MulAut.conj a⁻¹).toMonoidHom
          ≤ pCoreOf 2 (L.map (MulAut.conj a⁻¹).toMonoidHom) := map_pCoreOf_le (MulAut.conj a⁻¹) L
      _ = pCoreOf 2 L := by rw [map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ ha)]

theorem localDeltaTwoIn_eq_bot {K : Type*} [Group K] [Finite K] {A D H : Subgroup (MulAut K)}
    (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hDA : D ≤ A) (hD : D ≠ ⊥)
    (hAH : A ≤ Subgroup.normalizer (H : Set (MulAut K)))
    (hN : ∀ W : Subgroup (MulAut K), ¬ 3 ∣ Nat.card W →
      A ≤ Subgroup.normalizer (W : Set (MulAut K)) → W = ⊥) :
    localDeltaTwoIn H D = ⊥ := by
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun σ : MulAut K => (σ : K → K)) DFunLike.coe_injective
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨d₀, hd₀, hd₀1⟩ := (Subgroup.bot_or_exists_ne_one D).resolve_left hD
  refine hN _ ?_ ?_
  · have hle : localDeltaTwoIn H D ≤ pCoreOf 2 (H ⊓ Subgroup.centralizer {d₀}) :=
      iInf_le_of_le d₀ (iInf_le_of_le hd₀ (iInf_le_of_le hd₀1 le_rfl))
    have h2 : IsPGroup 2 ↥(localDeltaTwoIn H D) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le hle
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    norm_num at this
  · intro a haA
    have hnorm : ∀ d ∈ D, a ∈ Subgroup.normalizer
        (pCoreOf 2 (H ⊓ Subgroup.centralizer {d}) : Set (MulAut K)) := by
      intro d hd
      refine normalizer_le_normalizer_pCoreOf _ ?_
      have hC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set (MulAut K)) :
          Set (MulAut K)) :=
        Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hA a haA d (hDA hd)))
      rw [Subgroup.mem_normalizer_iff]
      intro n
      simp only [Subgroup.mem_inf]
      exact and_congr (Subgroup.mem_normalizer_iff.1 (hAH haA) n)
        (Subgroup.mem_normalizer_iff.1 hC n)
    rw [Subgroup.mem_normalizer_iff]
    intro n
    simp only [localDeltaTwoIn, Subgroup.mem_iInf]
    constructor
    · intro hn d hd hd1
      exact (Subgroup.mem_normalizer_iff.1 (hnorm d hd) n).1 (hn d hd hd1)
    · intro hn d hd hd1
      exact (Subgroup.mem_normalizer_iff.1 (hnorm d hd) n).2 (hn d hd hd1)

theorem balanced_of_noSig {K : Type*} [Group K] [Finite K] {A : Subgroup (MulAut K)}
    (hA : IsElemAbelian 3 A) (hA9 : Nat.card A = 9)
    (hN : ∀ W : Subgroup (MulAut K), ¬ 3 ∣ Nat.card W →
      A ≤ Subgroup.normalizer (W : Set (MulAut K)) → W = ⊥) :
    IsLocallyOTwoBalanced 3 2 A ∧ IsWeaklyLocallyOTwoBalanced 3 1 A := by
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun σ : MulAut K => (σ : K → K)) DFunLike.coe_injective
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hne : ∀ D : Subgroup (MulAut K), 1 < Nat.card D → D ≠ ⊥ := fun D hD h => by
    rw [h, Subgroup.card_bot] at hD
    exact lt_irrefl 1 hD
  refine ⟨fun D hD H _ hDH => ?_, fun D hD H _ hAH => ?_⟩
  · obtain ⟨hDA, -, hD9⟩ := hD
    have hDeq : D = A := Subgroup.eq_of_le_of_card_ge hDA (by rw [hA9, hD9]; norm_num)
    rw [hDeq] at hDH ⊢
    exact localDeltaTwoIn_eq_bot hcomm le_rfl (hne _ (by rw [hA9]; norm_num)) hDH hN
  · obtain ⟨hDA, -, hD3⟩ := hD
    rw [localDeltaTwoIn_eq_bot hcomm hDA (hne _ (by rw [hD3]; norm_num)) hAH hN]
    exact Subgroup.commutator_bot_left A

end Balance

section Inner

theorem genAut_or_noSig {S X : Type} [Group S] [Group X] [Finite S] [Finite X] (f : S ≃* X)
    (hcen : Subgroup.center S = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hK : ∀ P : Subgroup X, IsElemAbelian 3 P → Nat.card P = 9 → GenPlane P ∨ NoSignalizer P)
    {E : Subgroup (MulAut S)} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    GenAut E ∨ ∀ W : Subgroup (MulAut S), ¬ 3 ∣ Nat.card W →
      E ≤ Subgroup.normalizer (W : Set (MulAut S)) → W = ⊥ := by
  have hinj := CFSG.RankThree.PartTwo.Sec4.Item434Kit.conj_injective_of_center_eq_bot hcen
  have hEinn : ∀ φ ∈ E, φ ∈ (MulAut.conj : S →* MulAut S).range := fun φ hφ =>
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.mem_range_conj_of_pow_three hout (hE.2 φ hφ)
  set PS : Subgroup S := E.comap (MulAut.conj : S →* MulAut S) with hPS
  have hPSE : PS.map (MulAut.conj : S →* MulAut S) = E := by
    rw [hPS, Subgroup.map_comap_eq]
    exact inf_eq_right.2 fun φ hφ => hEinn φ hφ
  have hPSel : IsElemAbelian 3 PS :=
    CFSG.RankThree.PartTwo.Sec4.Item434Kit.isElemAbelian_of_map_injective hinj (hPSE ▸ hE)
  have hPScard : Nat.card PS = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, hPSE]
    exact hE9
  set PX : Subgroup X := PS.map f.toMonoidHom with hPX
  have hPXel : IsElemAbelian 3 PX := CFSG.Open.IsElemAbelian.map hPSel _
  have hPXcard : Nat.card PX = 9 := by
    rw [hPX, Subgroup.card_map_of_injective f.injective]
    exact hPScard
  rcases hK PX hPXel hPXcard with hG | hN
  · left
    rw [← hPSE]
    exact genAut_of_genPlane hcen (GenPlane.of_map f hG)
  · right
    intro T hT3 hET
    set g : MulAut S ≃* MulAut X := MulAut.congr f with hg
    have hY3 : ¬ 3 ∣ Nat.card (T.map g.toMonoidHom) := by
      rwa [Subgroup.card_map_of_injective g.injective]
    have hPY : PX.map (MulAut.conj : X →* MulAut X) ≤
        Subgroup.normalizer ((T.map g.toMonoidHom : Subgroup _) : Set (MulAut X)) := by
      rintro _ ⟨x, ⟨qs, hqs, rfl⟩, rfl⟩
      have hc : (MulAut.conj (f.toMonoidHom qs) : MulAut X) = g (MulAut.conj qs) := by
        ext y
        simp [hg, MulAut.conj_apply, MulAut.congr_apply]
      have hqE : (MulAut.conj qs : MulAut S) ∈ E := by
        rw [← hPSE]
        exact Subgroup.mem_map_of_mem _ hqs
      rw [show (MulAut.conj : X →* MulAut X) (f.toMonoidHom qs) = g (MulAut.conj qs) from hc]
      exact Subgroup.le_normalizer_map g.toMonoidHom (Subgroup.mem_map_of_mem _ (hET hqE))
    have hY1 := hN _ hY3 hPY
    rwa [Subgroup.map_eq_bot_iff_of_injective _ g.injective] at hY1

end Inner

section M12

open CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12
  CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig
open CFSG.RankThree.PartTwo.Sec4 (Item434AltPerm.exists_le_map_conj_of_card
  Item434AltPerm.map_conj_inv_le Item434AltPerm.map_conj_map_conj_inv
  Item434AltPerm.factorization_three_pow_mul)

theorem m12_vgen_parts :
    (∀ p ∈ m12VWordA ++ m12VWordB, p.1 < 3 ∧ p.2 ∈ idxV p.1) ∧ m12VProd m12VWordA = tA ∧
      m12VProd m12VWordB = tB := by
  have h := (Certificates.certificate232401 : m12VGenCheck = true)
  simp only [m12VGenCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_iff_mem] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem tbl_prod_elt_pairs (L : List (ℕ × Idx)) :
    tbl ((L.map fun p => elt p.2).prod).1 = m12VProd L := by
  induction L with
  | nil => exact tblG_one
  | cons p L ih =>
    rw [List.map_cons, List.prod_cons, tblG_mul, ih, tbl_elt]
    rfl

theorem ai_ne_one (i : Fin 3) :
    ai i ≠ 1 := by
  intro h
  have h1 := card_C i
  have h2 : Subgroup.centralizer ({ai i} : Set G12) = ⊤ := by
    rw [h]
    exact (Subgroup.eq_top_iff' _).mpr fun g =>
      Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
  rw [h2, Subgroup.card_top] at h1
  have h3 : Nat.card G12 = 95040 := CFSG.Sporadic.Mathieu.card_M12
  omega

theorem genPlane_A :
    GenPlane basisA.sub := by
  set T : Subgroup G12 := ⨆ (x : G12) (_ : x ∈ basisA.sub) (_ : x ≠ 1),
    pCoreOf 2 (Subgroup.centralizer {x}) with hT
  have hV : ∀ i : Fin 3, V i ≤ T := fun i => by
    have h1 : V i ≤ pCoreOf 2 (Subgroup.centralizer {ai i}) := (pCore_centralizer i).ge
    exact h1.trans (le_iSup_of_le (ai i) (le_iSup_of_le (mul_mem (pow_mem z_mem_A _) a_mem_A)
      (le_iSup_of_le (ai_ne_one i) le_rfl)))
  have hmem : ∀ p ∈ m12VWordA ++ m12VWordB, elt p.2 ∈ T := by
    intro p hp
    obtain ⟨hp3, hpk⟩ := m12_vgen_parts.1 p hp
    refine hV ⟨p.1, hp3⟩ ?_
    rw [mem_V, tbl_elt]
    exact List.mem_map.2 ⟨_, hpk, rfl⟩
  have hprod : ∀ L : List (ℕ × Idx), (∀ p ∈ L, elt p.2 ∈ T) →
      (L.map fun p => elt p.2).prod ∈ T := fun L hL => list_prod_mem fun g hg => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hg
    exact hL p hp
  have ha : CFSG.Sporadic.Mathieu.m12a = (m12VWordA.map fun p => elt p.2).prod := by
    rw [eq_iff_tbl, tbl_prod_elt_pairs, m12_vgen_parts.2.1]
    exact tbl_m12gA
  have hb : CFSG.Sporadic.Mathieu.m12b = (m12VWordB.map fun p => elt p.2).prod := by
    rw [eq_iff_tbl, tbl_prod_elt_pairs, m12_vgen_parts.2.2]
    exact tbl_m12gB
  have hcl : Subgroup.closure {CFSG.Sporadic.Mathieu.m12a, CFSG.Sporadic.Mathieu.m12b} ≤ T := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [ha]
      exact hprod _ fun p hp => hmem p (List.mem_append_left _ hp)
    · rw [hb]
      exact hprod _ fun p hp => hmem p (List.mem_append_right _ hp)
  intro g _
  exact hcl (CFSG.ComponentClassification.M12Cover.m12_closure_eq_top ▸ Subgroup.mem_top g)

theorem kill_m12
    (P : Subgroup G12) (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) :
    GenPlane P ∨ NoSignalizer P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hP0 : Nat.card P0 = 3 ^ (Nat.card G12).factorization 3 := by
    rw [card_P0]
    change 27 = 3 ^ (Nat.card CFSG.Blueprint.NativeSporadic.M12).factorization 3
    rw [CFSG.Sporadic.Mathieu.card_M12, show (95040 : ℕ) = 3 ^ 3 * 3520 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hP0 hPp
  set P' := P.map (MulAut.conj g⁻¹).toMonoidHom with hP'
  have hP'e : IsElemAbelian 3 P' := CFSG.Open.IsElemAbelian.map hP _
  have hmem : P' ∈ {B : Subgroup G12 | B ≤ P0 ∧ Nat.card B = 9} :=
    ⟨Item434AltPerm.map_conj_inv_le hg,
      by rw [hP', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]⟩
  rw [nine_eq] at hmem
  have hPeq : P = P'.map (MulAut.conj g).toMonoidHom :=
    (Item434AltPerm.map_conj_map_conj_inv P g).symm
  rcases hmem with h | h | h | h
  · right
    rw [h] at hP'e
    rw [hPeq, h]
    exact (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.noSignalizer_E hP'e).map_conj g
  · right
    rw [h] at hP'e
    rw [hPeq, h]
    exact (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.noSignalizer_F hP'e).map_conj g
  · left
    rw [hPeq, h]
    exact genPlane_A.map (MulAut.conj g)
  · left
    rw [Set.mem_singleton_iff] at h
    rw [hPeq, h]
    exact (GenPlane.of_map (MulAut.conj g0) (by rw [map_g0_A']; exact genPlane_A)).map
      (MulAut.conj g)

end M12

section J2

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.RankThree.PartTwo.Sec4 (Item434AltPerm.exists_le_map_conj_of_card
  Item434AltPerm.map_conj_inv_le Item434AltPerm.map_conj_map_conj_inv
  Item434AltPerm.factorization_three_pow_mul)

@[expose] noncomputable def j2VElt
    (j : ℕ) : GJ :=
  if h : j / 2 < 3 then vkE ⟨j / 2, h⟩ (j % 2 + 1) else 1

theorem rep_j2VElt {j : ℕ}
    (hj : j < 6) : Rep 315 (j2VArr j) (j2VElt j).1 := by
  have h : j / 2 < 3 := by omega
  rw [j2VElt, dif_pos h]
  exact rep_vkE ⟨j / 2, h⟩ (j % 2 + 1)

theorem rep_j2VProd :
    ∀ w : List ℕ, (∀ j ∈ w, j < 6) → Rep 315 (j2VProd w) ((w.map j2VElt).prod).1
  | [], _ => by
    show Rep 315 (idA 315) (1 : GJ).1
    exact rep_idA
  | j :: w, hw => by
    rw [j2VProd, List.map_cons, List.prod_cons, Subgroup.coe_mul]
    exact rep_compA (rep_j2VElt (hw j (by simp))) (rep_j2VProd w fun k hk => hw k (by simp [hk]))

theorem j2_vgen_parts :
    (∀ j ∈ j2VWordA ++ j2VWordB, j < 6) ∧ eqA 315 (j2VProd j2VWordA) autStrong[0]! = true ∧
      eqA 315 (j2VProd j2VWordB) autStrong[1]! = true := by
  have h := (Certificates.certificate232402 : j2VGenCheck = true)
  simp only [j2VGenCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem aJ_ne_one
    (k : Fin 3) : aJ k ≠ 1 := by
  intro h
  have hc := (c_spec k).2
  rw [h] at hc
  apply xJ_ne_one
  calc xJ = (cJ k)⁻¹ * (cJ k * xJ * (cJ k)⁻¹) * cJ k := by group
    _ = 1 := by rw [hc]; group

theorem genPlane_E0 :
    GenPlane (Ej 0) := by
  set T : Subgroup GJ := ⨆ (x : GJ) (_ : x ∈ Ej 0) (_ : x ≠ 1),
    pCoreOf 2 (Subgroup.centralizer {x}) with hT
  have hV : ∀ k : Fin 3, VkJ k ≤ T := fun k => by
    have h1 : VkJ k ≤ pCoreOf 2 (Subgroup.centralizer {aJ k}) := (pCore_centralizer_a k).ge
    exact h1.trans (le_iSup_of_le (aJ k) (le_iSup_of_le (aJ_mem_E0 k)
      (le_iSup_of_le (aJ_ne_one k) le_rfl)))
  have hmem : ∀ j < 6, j2VElt j ∈ T := by
    intro j hj
    have h : j / 2 < 3 := by omega
    rw [j2VElt, dif_pos h]
    exact hV ⟨j / 2, h⟩ (vkE_mem _ _)
  have hprod : ∀ w : List ℕ, (∀ j ∈ w, j < 6) → (w.map j2VElt).prod ∈ T := fun w hw =>
    list_prod_mem fun g hg => by
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
      exact hmem j (hw j hj)
  obtain ⟨hw, hA, hB⟩ := j2_vgen_parts
  have hwA : ∀ j ∈ j2VWordA, j < 6 := fun j hj => hw j (List.mem_append_left _ hj)
  have hwB : ∀ j ∈ j2VWordB, j < 6 := fun j hj => hw j (List.mem_append_right _ hj)
  have hcl : Subgroup.closure ({permA, permB} : Set (Equiv.Perm (Fin 315))) ≤
      T.map (CFSG.ComponentClassification.J2Cover.P).subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hprod _ hwA, eq_of_eqA (rep_j2VProd _ hwA) rep_permA hA⟩
    · exact ⟨_, hprod _ hwB, eq_of_eqA (rep_j2VProd _ hwB) rep_permB hB⟩
  intro g _
  obtain ⟨t, ht, htg⟩ := hcl g.2
  rw [show g = t from Subtype.ext htg.symm]
  exact ht

theorem kill_j2
    (P : Subgroup GJ) (_hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) : GenPlane P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hP3 : Nat.card P3 = 3 ^ (Nat.card GJ).factorization 3 := by
    rw [card_P3]
    change 27 = 3 ^ (Nat.card CFSG.ComponentClassification.J2Cover.P).factorization 3
    rw [CFSG.ComponentClassification.J2Cover.card_P, show (604800 : ℕ) = 3 ^ 3 * 22400 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 3 (by norm_num)]
    norm_num
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hP3 hPp
  have hle := Item434AltPerm.map_conj_inv_le hg
  have hmem : P.map (MulAut.conj g⁻¹).toMonoidHom ∈
      {B : Subgroup GJ | B ≤ P3 ∧ Nat.card B = 9} :=
    ⟨hle, by rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]⟩
  rw [nine_eq] at hmem
  obtain ⟨j, hj⟩ := hmem
  obtain ⟨n, -, hn⟩ := exists_conj_E0 j
  have hPeq : P = ((Ej 0).map (MulAut.conj n⁻¹).toMonoidHom).map
      (MulAut.conj g).toMonoidHom := by
    rw [← Item434AltPerm.map_conj_map_conj_inv P g, ← hj, ← hn]
    rfl
  rw [hPeq]
  exact (genPlane_E0.map (MulAut.conj n⁻¹)).map (MulAut.conj g)

end J2

section M22

open CFSG.RankThree.PartTwo.Sec4.Item434SporGen CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.ComponentClassification.WittDesign CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 (kleinSub mem_kleinSub isPGroup_kleinSub)
open CFSG.RankThree.PartTwo.Sec4 (Item434AltPerm.exists_le_map_conj_of_card
  Item434AltPerm.factorization_three_pow_mul)

abbrev M22G : Type := ↥CFSG.Blueprint.NativeSporadic.M22

theorem m22_elt_parts :
    eqA 22 (compA 22 m22E1 m22E2) m22E12 = true ∧
    (∀ k < 6, isInvA 22 (m22VArr k) (invCand 22 (m22VArr k)) = true ∧
      siftA 22 (rawLevels 22 (CFSG.EvenSmallLie.OmegaEight.pushWords 22 m22SigArrs m22Words)
        (m22Base.map Fin.val).toArray) (m22Base.map Fin.val).toArray 0 (m22VArr k) = true ∧
      eqA 22 (compA 22 (m22VArr k) (m22VArr k)) (idA 22) = true) ∧
    ∀ j < 3, eqA 22 (m22EArr j) (idA 22) = false ∧
      eqA 22 (compA 22 (m22VArr (2 * j)) (m22VArr (2 * j + 1)))
        (compA 22 (m22VArr (2 * j + 1)) (m22VArr (2 * j))) = true ∧
      eqA 22 (compA 22 (m22VArr (2 * j)) (m22EArr j))
        (compA 22 (m22EArr j) (m22VArr (2 * j))) = true ∧
      eqA 22 (compA 22 (m22VArr (2 * j + 1)) (m22EArr j))
        (compA 22 (m22EArr j) (m22VArr (2 * j + 1))) = true := by
  have h := (Certificates.certificate232403).1
  simp only [m22VEltCheck, m22Levels, m22GenS, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun k hk => ?_, fun j hj => ?_⟩
  · have := allLt_spec h2 hk
    simp only [Bool.and_eq_true] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := allLt_spec h3 hj
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
    exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem m22_vgen_parts :
    (∀ k ∈ m22VWordA ++ m22VWordB, k < 6) ∧ eqA 22 (m22VProd m22VWordA) m22GenA = true ∧
      eqA 22 (m22VProd m22VWordB) m22GenB = true := by
  have h := (Certificates.certificate232403).2.2.2.2
  simp only [m22VGenCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem m22BadB_eq_false {j : ℕ}
    (hj : j < 3) (x : M22G) : m22BadB j ⇑x.1 = false := by
  have h0 : m22Count (fun g => m22BadB j g = true) = 0 := by
    have h := (Certificates.certificate232403)
    interval_cases j
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
  rw [← card_m22_subtype] at h0
  by_contra hx
  have hne : Nonempty {y : M22 // m22BadB j ⇑(y : Equiv.Perm (Fin 22)) = true} :=
    ⟨⟨x, by simpa using hx⟩⟩
  exact (Nat.card_pos_iff.2 ⟨hne, inferInstance⟩).ne' h0

theorem rep_m22VArr {k : ℕ} (hk : k < 6) :
    Rep 22 (m22VArr k) (permOfArr 22 (m22VArr k)) :=
  (rep_permOfArr (m22_elt_parts.2.1 k hk).1).1

@[expose] noncomputable def m22V
    (k : ℕ) : M22G :=
  if hk : k < 6 then
    ⟨permOfArr 22 (m22VArr k), closure_m22Sig ▸ mem_closure_of_sift (D := m22Words) (by norm_num)
      (by decide) (by norm_num) m22_chain (rep_m22VArr hk) (m22_elt_parts.2.1 k hk).2.1⟩
  else 1

theorem rep_m22V
    {k : ℕ} (hk : k < 6) : Rep 22 (m22VArr k) (m22V k).1 := by
  rw [m22V, dif_pos hk]
  exact rep_m22VArr hk

@[expose] noncomputable def m22eE
    (j : ℕ) : M22G :=
  if j = 0 then m22e1 else if j = 1 then m22e2 else m22e1 * m22e2

theorem rep_m22eE
    (j : ℕ) : Rep 22 (m22EArr j) (m22eE j).1 := by
  unfold m22eE m22EArr
  split_ifs
  · exact rep_m22E1
  · exact rep_m22E2
  · exact rep_of_eqA (rep_compA rep_m22E1 rep_m22E2) m22_elt_parts.1

theorem m22eE_mem (j : ℕ) :
    m22eE j ∈ Subgroup.closure ({m22e1, m22e2} : Set M22G) := by
  unfold m22eE
  split_ifs
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

theorem m22eE_ne_one
    {j : ℕ} (hj : j < 3) : m22eE j ≠ 1 := by
  intro h
  have h2 : eqA 22 (m22EArr j) (idA 22) = true :=
    (eqA_iff (rep_m22eE j) rep_idA).2 (by rw [h]; rfl)
  rw [(m22_elt_parts.2.2 j hj).1] at h2
  exact Bool.noConfusion h2

theorem m22V_sq
    {k : ℕ} (hk : k < 6) : m22V k * m22V k = 1 :=
  Subtype.ext (eq_of_eqA (rep_compA (rep_m22V hk) (rep_m22V hk)) rep_idA
    (m22_elt_parts.2.1 k hk).2.2)

theorem m22V_comm
    (j : Fin 3) :
    m22V (2 * j) * m22V (2 * j + 1) = m22V (2 * j + 1) * m22V (2 * j) :=
  Subtype.ext (eq_of_eqA (rep_compA (rep_m22V (by omega)) (rep_m22V (by omega)))
    (rep_compA (rep_m22V (by omega)) (rep_m22V (by omega))) (m22_elt_parts.2.2 j j.2).2.1)

theorem m22V_comm_e
    (j : Fin 3) :
    m22V (2 * j) * m22eE j = m22eE j * m22V (2 * j) ∧
      m22V (2 * j + 1) * m22eE j = m22eE j * m22V (2 * j + 1) :=
  ⟨Subtype.ext (eq_of_eqA (rep_compA (rep_m22V (by omega)) (rep_m22eE j))
      (rep_compA (rep_m22eE j) (rep_m22V (by omega))) (m22_elt_parts.2.2 j j.2).2.2.1),
    Subtype.ext (eq_of_eqA (rep_compA (rep_m22V (by omega)) (rep_m22eE j))
      (rep_compA (rep_m22eE j) (rep_m22V (by omega))) (m22_elt_parts.2.2 j j.2).2.2.2)⟩

@[expose] noncomputable def m22VSub
    (j : Fin 3) : Subgroup M22G :=
  kleinSub (m22V_sq (k := 2 * j) (by omega)) (m22V_sq (k := 2 * j + 1) (by omega)) (m22V_comm j)

theorem m22Fn_eq {t : Array ℕ} {g : Equiv.Perm (Fin 22)} (h : Rep 22 t g) : m22Fn t = ⇑g := by
  funext x
  apply Fin.ext
  show t[x.val]! % 22 = (g x : ℕ)
  rw [h x, Nat.mod_eq_of_lt (g x).2]

theorem m22Intertw_iff (g u w : Equiv.Perm (Fin 22)) :
    m22Intertw ⇑g ⇑u ⇑w = true ↔ g * u = w * g := by
  rw [m22Intertw, List.all_eq_true]
  constructor
  · intro h
    refine Equiv.ext fun x => ?_
    have := h x (List.mem_finRange x)
    rw [beq_iff_eq] at this
    exact this
  · rintro h x -
    rw [beq_iff_eq]
    exact congrArg (fun σ : Equiv.Perm (Fin 22) => σ x) h

theorem conj_eq_of_mul_eq {G : Type*} [Group G] {g u x : G} (h : g * u = x * g) :
    g * u * g⁻¹ = x := by
  rw [h]
  group

theorem m22_conj_facts
    (j : Fin 3) {g : M22G}
    (hg : g ∈ Subgroup.centralizer {m22eE j}) :
    g * m22V (2 * j) * g⁻¹ ∈ m22VSub j ∧ g * m22V (2 * j + 1) * g⁻¹ ∈ m22VSub j := by
  have hv := rep_m22V (k := 2 * j) (by omega)
  have hw := rep_m22V (k := 2 * j + 1) (by omega)
  have hb := m22BadB_eq_false j.2 g
  rw [m22BadB, m22NormB, m22Fn_eq (rep_m22eE j), m22Fn_eq hv, m22Fn_eq hw,
    m22Fn_eq (rep_compA hv hw)] at hb
  have hge : m22Intertw ⇑g.1 ⇑(m22eE j).1 ⇑(m22eE j).1 = true := by
    rw [m22Intertw_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hg)
  rw [hge, Bool.true_and, Bool.not_eq_false', Bool.and_eq_true] at hb
  simp only [m22ConjIn, Bool.or_eq_true, m22Intertw_iff] at hb
  have hmem : ∀ u x : M22G, g.1 * u.1 = x.1 * g.1 → x ∈ m22VSub j →
      g * u * g⁻¹ ∈ m22VSub j := by
    intro u x h hx
    rw [conj_eq_of_mul_eq (Subtype.ext h : g * u = x * g)]
    exact hx
  have hvm : m22V (2 * j) ∈ m22VSub j := mem_kleinSub.2 (Or.inr (Or.inl rfl))
  have hwm : m22V (2 * j + 1) ∈ m22VSub j := mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl)))
  have hvwm : m22V (2 * j) * m22V (2 * j + 1) ∈ m22VSub j :=
    mem_kleinSub.2 (Or.inr (Or.inr (Or.inr rfl)))
  obtain ⟨h1, h2⟩ := hb
  refine ⟨?_, ?_⟩
  · rcases h1 with (h | h) | h
    · exact hmem _ _ h hvm
    · exact hmem _ _ h hwm
    · exact hmem _ (m22V (2 * j) * m22V (2 * j + 1)) h hvwm
  · rcases h2 with (h | h) | h
    · exact hmem _ _ h hvm
    · exact hmem _ _ h hwm
    · exact hmem _ (m22V (2 * j) * m22V (2 * j + 1)) h hvwm

theorem m22VSub_le
    (j : Fin 3) :
    m22VSub j ≤ pCoreOf 2 (Subgroup.centralizer {m22eE j}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hve, hwe⟩ := m22V_comm_e j
  have key : ∀ g ∈ Subgroup.centralizer ({m22eE j} : Set M22G), ∀ u ∈ m22VSub j,
      g * u * g⁻¹ ∈ m22VSub j := by
    intro g hg u hu
    obtain ⟨h1, h2⟩ := m22_conj_facts j hg
    rcases mem_kleinSub.1 hu with rfl | rfl | rfl | rfl
    · rw [mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · exact h1
    · exact h2
    · have e : g * (m22V (2 * j) * m22V (2 * j + 1)) * g⁻¹ =
          (g * m22V (2 * j) * g⁻¹) * (g * m22V (2 * j + 1) * g⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ h1 h2
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_ isPGroup_kleinSub
  · intro u hu
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases mem_kleinSub.1 hu with rfl | rfl | rfl | rfl
    · rw [one_mul, mul_one]
    · exact hve
    · exact hwe
    · rw [mul_assoc, hwe, ← mul_assoc, hve, mul_assoc]
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨key g hg n, fun hn => ?_⟩
    have h := key g⁻¹ (Subgroup.inv_mem _ hg) _ hn
    have e : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
    rwa [e] at h

theorem rep_m22VProd :
    ∀ w : List ℕ, (∀ k ∈ w, k < 6) → Rep 22 (m22VProd w) ((w.map m22V).prod).1
  | [], _ => by
    show Rep 22 (idA 22) (1 : M22G).1
    exact rep_idA
  | k :: w, hw => by
    rw [m22VProd, List.map_cons, List.prod_cons, Subgroup.coe_mul]
    exact rep_compA (rep_m22V (hw k (by simp))) (rep_m22VProd w fun i hi => hw i (by simp [hi]))

theorem genPlane_m22E :
    GenPlane (Subgroup.closure ({m22e1, m22e2} : Set M22G)) := by
  set T : Subgroup M22G := ⨆ (x : M22G) (_ : x ∈ Subgroup.closure ({m22e1, m22e2} : Set M22G))
    (_ : x ≠ 1), pCoreOf 2 (Subgroup.centralizer {x}) with hT
  have hV : ∀ j : Fin 3, m22VSub j ≤ T := fun j =>
    (m22VSub_le j).trans (le_iSup_of_le (m22eE j) (le_iSup_of_le (m22eE_mem j)
      (le_iSup_of_le (m22eE_ne_one j.2) le_rfl)))
  have hmem : ∀ k < 6, m22V k ∈ T := by
    intro k hk
    have hj : k / 2 < 3 := by omega
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have e : m22V k = m22V (2 * (⟨k / 2, hj⟩ : Fin 3)) := by
        congr 1
        simp only
        omega
      rw [e]
      exact hV ⟨k / 2, hj⟩ (mem_kleinSub.2 (Or.inr (Or.inl rfl)))
    · have e : m22V k = m22V (2 * (⟨k / 2, hj⟩ : Fin 3) + 1) := by
        congr 1
        simp only
        omega
      rw [e]
      exact hV ⟨k / 2, hj⟩ (mem_kleinSub.2 (Or.inr (Or.inr (Or.inl rfl))))
  have hprod : ∀ w : List ℕ, (∀ k ∈ w, k < 6) → (w.map m22V).prod ∈ T := fun w hw =>
    list_prod_mem fun g hg => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hg
      exact hmem k (hw k hk)
  obtain ⟨hw, hA, hB⟩ := m22_vgen_parts
  have hwA : ∀ k ∈ m22VWordA, k < 6 := fun k hk => hw k (List.mem_append_left _ hk)
  have hwB : ∀ k ∈ m22VWordB, k < 6 := fun k hk => hw k (List.mem_append_right _ hk)
  have hcl : Subgroup.closure ({CFSG.Sporadic.Mathieu.m22gA, CFSG.Sporadic.Mathieu.m22gB} :
      Set (Equiv.Perm (Fin 22))) ≤ T.map (CFSG.Blueprint.NativeSporadic.M22).subtype := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hprod _ hwA, eq_of_eqA (rep_m22VProd _ hwA) rep_m22GenA hA⟩
    · exact ⟨_, hprod _ hwB, eq_of_eqA (rep_m22VProd _ hwB) rep_m22GenB hB⟩
  intro g _
  obtain ⟨t, ht, htg⟩ := hcl (by rw [← CFSG.Sporadic.Mathieu.m22_eq]; exact g.2)
  rw [show g = t from Subtype.ext htg.symm]
  exact ht

theorem kill_m22
    (P : Subgroup M22G) (_hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) : GenPlane P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : Nat.card (Subgroup.closure ({m22e1, m22e2} : Set M22G)) =
      3 ^ (Nat.card M22G).factorization 3 := by
    rw [card_m22E, CFSG.Sporadic.Mathieu.card_M22, show (443520 : ℕ) = 3 ^ 2 * 49280 by norm_num,
      Item434AltPerm.factorization_three_pow_mul 2 (by norm_num)]
    norm_num
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hE hPp
  have hcard : Nat.card ((Subgroup.closure ({m22e1, m22e2} : Set M22G)).map
      (MulAut.conj g).toMonoidHom) ≤ Nat.card P := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_m22E, hP9]
  rw [Subgroup.eq_of_le_of_card_ge hg hcard]
  exact genPlane_m22E.map (MulAut.conj g)

end M22

section Main

theorem center_quot_eq_bot {Y : Type} [Group Y] (hq : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  haveI : IsSimpleGroup (Y ⧸ Subgroup.center Y) := hq.2
  exact CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup
    (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq)

theorem top_le_of_model {Y X : Type} [Group Y] [Finite Y] [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple Y) (hO : GLAPPrimeCore 3 Y = ⊥) (f : (Y ⧸ Subgroup.center Y) ≃* X)
    (hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2)
    (hrank : CFSG.HardMathSupport.Dickson.I271.AutRankLe2 3 (Y ⧸ Subgroup.center Y))
    (hK : ∀ P : Subgroup X, IsElemAbelian 3 P → Nat.card P = 9 → GenPlane P ∨ NoSignalizer P)
    {A : Subgroup (MulAut Y)} (hA : IsElemAbelian 3 A) (hA9 : 9 ≤ Nat.card A)
    (hbal : ¬ IsLocallyOTwoBalanced 3 2 A ∨ ¬ IsWeaklyLocallyOTwoBalanced 3 1 A) :
    (⊤ : Subgroup Y) ≤ ⨆ (α : MulAut Y) (_ : α ∈ A) (_ : α ≠ 1),
      GLAPPrimeCoreOf 3 (fixSub α) := by
  have hperf : commutator Y = ⊤ := hq.1
  have hZ : IsPGroup 3 ↥(Subgroup.center Y) :=
    AltFacts2.isPGroup_center_of_core_eq_bot Nat.prime_three hO
  have hφ := quotientCenterAut'_injective hperf
  have hĀ : IsElemAbelian 3 (A.map (quotientCenterAut' Y)) := CFSG.Open.IsElemAbelian.map hA _
  have hĀcard : Nat.card (A.map (quotientCenterAut' Y)) = Nat.card A :=
    Subgroup.card_map_of_injective hφ
  have hĀ9 : Nat.card (A.map (quotientCenterAut' Y)) = 9 := by
    have h1 := hrank _ hĀ
    rw [hĀcard] at h1 ⊢
    norm_num at h1
    omega
  have hout3 : ¬ 3 ∣ Nat.card (Outer (Y ⧸ Subgroup.center Y)) := by
    intro hd
    have hpos : 0 < Nat.card (Outer (Y ⧸ Subgroup.center Y)) := Nat.card_pos
    have := Nat.le_of_dvd hpos hd
    omega
  rcases genAut_or_noSig f (center_quot_eq_bot hq) hout3 hK hĀ hĀ9 with hg | hn
  · exact top_le_of_genAut hperf hZ hg
  · exfalso
    obtain ⟨h1, h2⟩ := balanced_of_noSig hA (hĀcard ▸ hĀ9) (noSig_of_quot hperf hn)
    rcases hbal with h | h
    · exact h h1
    · exact h h2

open CFSG.ComponentClassification.OuterAutomorphisms (equivalence) in
open CFSG.HardMathSupport.Dickson.I271 (autRankLe2_of_offPair) in
open CFSG.HardMathSupport.Timmesfeld.Tables.Census (offPair_M12 offPair_M22 offPair_J2) in
theorem input23_24Q_holds :
    Inputs123b.Input23_24Q := by
  intro Y _ _ s hq hO hs hsp A hA hA9 hbal
  have hcen := center_quot_eq_bot hq
  obtain ⟨e₀⟩ := hsp
  rcases hs with rfl | rfl | rfl
  ·
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
    let f : (Y ⧸ Subgroup.center Y) ≃* ↥CFSG.Blueprint.NativeSporadic.M12 := e₀.trans b.symm
    have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 :=
      ((Nat.card_congr (equivalence f).toEquiv).trans
        CFSG.ComponentClassification.M12Cover.card_outer).le
    exact top_le_of_model hq hO f hout
      (autRankLe2_of_offPair Nat.prime_three (by norm_num) (by decide) offPair_M12 f hcen hout)
      kill_m12 hA hA9 hbal
  ·
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
    let f : (Y ⧸ Subgroup.center Y) ≃* ↥CFSG.Blueprint.NativeSporadic.M22 := e₀.trans b.symm
    have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
      rw [Nat.card_congr (equivalence f).toEquiv]
      exact CFSG.RankThree.PartTwo.Sec4.card_outer_le_two_of_card_mulAut_le
        CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card
    exact top_le_of_model hq hO f hout
      (autRankLe2_of_offPair Nat.prime_three (by norm_num) (by decide) offPair_M22 f hcen hout)
      (fun P hP hP9 => Or.inl (kill_m22 P hP hP9)) hA hA9 hbal
  ·
    obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
    let fC : (Y ⧸ Subgroup.center Y) ≃* CFSG.Blueprint.NativeSporadic.J2 := e₀.trans b.symm
    have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := by
      rw [Nat.card_congr (equivalence fC).toEquiv]
      exact CFSG.Sporadic.Schreier.AT_J2_Schreier.1
    exact top_le_of_model hq hO (fC.trans CFSG.ComponentClassification.J2Cover.nativeEquivP) hout
      (autRankLe2_of_offPair Nat.prime_three (by norm_num) (by decide) offPair_J2 fC hcen hout)
      (fun P hP hP9 => Or.inl (kill_j2 P hP hP9)) hA hA9 hbal

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2324Q
