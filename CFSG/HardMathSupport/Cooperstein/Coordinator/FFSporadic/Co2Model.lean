module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2D1
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Engine
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Heis
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Local
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Rank
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Split
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KernelTrivialThreeCo2
public import CFSG.Sporadic.Co2Schreier.FullAut
public import CFSG.Sporadic.Co2Schreier.InvolClasses
public import CFSG.Sporadic.Presentation.Co2Exact
public import CFSG.Sporadic.Recognition.Co2MultiplierCert

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Blueprint
open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert
open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Engine

theorem not_dvd_card_center_of_kernelTrivial {X : Type} [Group X] {p : ℕ} [hp : Fact p.Prime]
    (h : CFSG.AGLEmbedding.KernelTrivialAt X p) {L : Type} [Group L] [Finite L]
    [Group.IsPerfect L] (e : L ⧸ Subgroup.center L ≃* X) :
    ¬ p ∣ Nat.card (Subgroup.center L) := by
  intro hdvd
  classical
  set Z := Subgroup.center L with hZ
  set m := ordCompl[p] (Nat.card Z) with hm
  have hZcomm : ∀ a ∈ Z, ∀ b : L, a * b = b * a := fun a ha b =>
    (Subgroup.mem_center_iff.1 ha b).symm
  let Q : Subgroup L :=
    { carrier := {x | x ∈ Z ∧ x ^ m = 1}
      mul_mem' := fun {a b} ha hb => ⟨Z.mul_mem ha.1 hb.1, by
        rw [(Commute.mul_pow (hZcomm a ha.1 b)), ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨Z.one_mem, one_pow m⟩
      inv_mem' := fun {a} ha => ⟨Z.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hQZ : Q ≤ Z := fun x hx => hx.1
  have hQn : Q.Normal := ⟨fun n hn g => by
    rw [← hZcomm n hn.1 g, mul_inv_cancel_right]
    exact hn⟩
  have : Group.IsPerfect (L ⧸ Q) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  let π : L ⧸ Q →* X := e.toMonoidHom.comp (QuotientGroup.map Q Z (MonoidHom.id L) hQZ)
  have hπ : ∀ x : L, π (x : L ⧸ Q) = e (x : L ⧸ Z) := fun x => rfl
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
    exact ⟨x, rfl⟩
  have hker : ∀ y : L ⧸ Q, π y = 1 → ∃ x ∈ Z, y = (x : L ⧸ Q) := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff] at hy
    exact ⟨x, hy, rfl⟩
  have hcen : π.ker ≤ Subgroup.center (L ⧸ Q) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hker y hy
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hZcomm x hx w]
  have hpk : IsPGroup p π.ker := by
    intro y
    obtain ⟨x, hx, hxy⟩ := hker y y.2
    refine ⟨(Nat.card Z).factorization p, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, hxy, ← QuotientGroup.mk_pow, Subgroup.coe_one,
      QuotientGroup.eq_one_iff]
    refine ⟨Z.pow_mem hx _, ?_⟩
    rw [← pow_mul, hm, Nat.ordProj_mul_ordCompl_eq_self]
    have h2 : (⟨x, hx⟩ : Z) ^ Nat.card Z = 1 := pow_card_eq_one'
    have h3 := congrArg Subtype.val h2
    rw [Subgroup.coe_pow, Subgroup.coe_one] at h3
    exact h3
  have hbot := h (L ⧸ Q) π hπs hcen hpk
  obtain ⟨zz, hzz⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hzQ : ((zz : L) : L ⧸ Q) ∈ π.ker := by
    rw [MonoidHom.mem_ker, hπ, ← map_one e, e.injective.eq_iff, QuotientGroup.eq_one_iff]
    exact zz.2
  rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzQ
  have hdm : p ∣ m := by
    have h1 : orderOf (zz : L) ∣ m := orderOf_dvd_of_pow_eq_one hzQ.2
    rwa [Subgroup.orderOf_coe, hzz] at h1
  have hcop := Nat.coprime_ordCompl hp.out (Nat.card_pos (α := Z)).ne'
  rw [← hm] at hcop
  exact hp.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop hdm)

theorem exists_subgroup_map {A B : Type*} [Group A] [Group B] (e : A ≃* B) (S : Subgroup A) :
    ∃ T : Subgroup B, (∀ y, y ∈ T ↔ ∃ x ∈ S, e x = y) ∧ Nat.card T = Nat.card S := by
  refine ⟨S.map e.toMonoidHom, fun y => ?_, ?_⟩
  · rw [Subgroup.mem_map]
    rfl
  · exact Subgroup.card_map_of_injective e.injective

section Sub

variable {Γ : Type*} [Group Γ] (P : Subgroup Γ)

theorem centralizer_mk_eq' {x : Γ} (hx : x ∈ P) :
    Subgroup.centralizer {(⟨x, hx⟩ : P)} = (P ⊓ Subgroup.centralizer {x}).subgroupOf P := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff, Subtype.ext_iff]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem sup_eq_top_subgroupOf {S1 S2 : Subgroup Γ} (h1 : S1 ≤ P) (h2 : S2 ≤ P)
    (h : P ≤ S1 ⊔ S2) : S1.subgroupOf P ⊔ S2.subgroupOf P = ⊤ := by
  rw [← Subgroup.subgroupOf_sup h1 h2, Subgroup.subgroupOf_eq_top]
  exact h

end Sub

section Model

theorem heis_sub {p n : ℕ} {t : Equiv.Perm (Fin 2300)} (ht : t ∈ co2P)
    (h : ∃ (x y : Fin (n + 1) → Equiv.Perm (Fin 2300)) (w : Equiv.Perm (Fin 2300)),
      (∀ i, x i ∈ co2P) ∧ (∀ i, y i ∈ co2P) ∧ w ∈ co2P ∧ HeisCfg p (n + 1) x y w ∧
      (∀ i, y i ^ p = 1) ∧ t * x 0 * t⁻¹ = (x 0)⁻¹) :
    ∃ (x y : Fin (n + 1) → co2P) (w : co2P), HeisCfg p (n + 1) x y w ∧ (∀ i, y i ^ p = 1) ∧
      (⟨t, ht⟩ : co2P) * x 0 * (⟨t, ht⟩ : co2P)⁻¹ = (x 0)⁻¹ := by
  obtain ⟨x, y, w, hx, hy, hw, hc, hyp, hinv⟩ := h
  have hfz : (MonoidHom.id co2P) ⟨w, hw⟩ ≠ 1 := fun h1 => hc.z1 (by
    have := congrArg Subtype.val h1
    simpa using this)
  refine ⟨fun i => ⟨x i, hx i⟩, fun i => ⟨y i, hy i⟩, ⟨w, hw⟩,
    HeisCfg.ofSubgroup co2P (MonoidHom.id co2P) hx hy hw hc hfz, fun i => ?_, ?_⟩
  · apply Subtype.ext
    simpa using hyp i
  · apply Subtype.ext
    simpa using hinv

theorem co2CutData_nonempty : Nonempty (Co2CutData co2P) := by
  obtain ⟨zp, fp, hzp, hfp, hzz, hff, hzf, hne, hzft, ⟨g1, hg1, hg1e⟩, ⟨g2, hg2, hg2e⟩, hg₁, hg₂,
    hg₃⟩ := Co2.d1_ambient
  have hNN_le : Co2.NN zp fp ≤ co2P := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨c, hc, rfl | rfl⟩
    · exact co2P.mul_mem (co2P.mul_mem hc.1 hzp) (co2P.inv_mem hc.1)
    · exact co2P.mul_mem (co2P.mul_mem hc.1 hfp) (co2P.inv_mem hc.1)
  have hcz_le : co2P ⊓ Subgroup.centralizer {zp} ≤ co2P := inf_le_left
  have hcf_le : co2P ⊓ Subgroup.centralizer {fp} ≤ co2P := inf_le_left
  have hNconj : Nconj (⟨zp, hzp⟩ : co2P) ⟨fp, hfp⟩ = (Co2.NN zp fp).subgroupOf co2P := by
    have hmap : (Nconj (⟨zp, hzp⟩ : co2P) ⟨fp, hfp⟩).map co2P.subtype = Co2.NN zp fp := by
      rw [Nconj, MonoidHom.map_closure, Co2.NN]
      congr 1
      ext y
      constructor
      · rintro ⟨y', ⟨c, hc, hy'⟩, rfl⟩
        have hct : (c : Equiv.Perm (Fin 2300)) * (zp * fp) = (zp * fp) * c := by
          have := congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)
          simpa using this
        refine ⟨c, ⟨c.2, ?_⟩, ?_⟩
        · exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← hzft]; exact hct)
        · rcases hy' with rfl | rfl
          · left; rfl
          · right; rfl
      · rintro ⟨c, ⟨hcP, hcc⟩, hy⟩
        have hct : (⟨c, hcP⟩ : co2P) ∈ Subgroup.centralizer
            {(⟨zp, hzp⟩ : co2P) * ⟨fp, hfp⟩} := by
          rw [Subgroup.mem_centralizer_singleton_iff]
          apply Subtype.ext
          have := Subgroup.mem_centralizer_singleton_iff.1 hcc
          rw [← hzft] at this
          exact this
        rcases hy with rfl | rfl
        · exact ⟨_, ⟨⟨c, hcP⟩, hct, Or.inl rfl⟩, rfl⟩
        · exact ⟨_, ⟨⟨c, hcP⟩, hct, Or.inr rfl⟩, rfl⟩
    rw [Co2.NN] at hmap ⊢
    show _ = (Subgroup.closure _).comap co2P.subtype
    rw [← hmap, Subgroup.comap_map_eq_self_of_injective co2P.subtype_injective]
  have hcentz : Subgroup.centralizer {zP} = locC.subgroupOf co2P := by
    rw [locC_eq_centralizer]
    exact centralizer_mk_eq' co2P locZ_mem
  refine ⟨{ z0 := zP
            Q0 := locQ.subgroupOf co2P
            a := ⟨zp, hzp⟩
            b := ⟨fp, hfp⟩
            t1 := tP
            t2 := uP
            z0_inv := ?_
            ha := ?_
            hb := ?_
            hab_comm := ?_
            hab_ne := ?_
            gen₁ := ?_
            gen₂ := ?_
            gen₃ := ?_
            dich := ?_
            Q_rank := ?_
            noA_rank := ?_
            classes := ?_
            heisA := ?_
            heisB := ?_
            heisC := ?_ }⟩
  · have h1 := myRep_sq (r := 0) (by norm_num)
    have h2 := myRep_ne_one (r := 0) (by norm_num)
    rw [myRep_zero] at h1 h2
    exact ⟨h1, h2⟩
  · exact isConj_iff.2 ⟨⟨g1, hg1⟩, Subtype.ext hg1e⟩
  · exact isConj_iff.2 ⟨⟨g2, hg2⟩, Subtype.ext hg2e⟩
  · exact Subtype.ext hzf
  · exact fun h => hne (congrArg Subtype.val h)
  · rw [centralizer_mk_eq' co2P hzp, centralizer_mk_eq' co2P hfp]
    exact sup_eq_top_subgroupOf co2P inf_le_left inf_le_left hg₁
  · rw [centralizer_mk_eq' co2P hzp, hNconj]
    exact sup_eq_top_subgroupOf co2P inf_le_left hNN_le hg₂
  · rw [centralizer_mk_eq' co2P hfp, hNconj]
    exact sup_eq_top_subgroupOf co2P inf_le_left hNN_le hg₃
  · intro N hN1 hN2
    have hmemC : ∀ g : co2P, g ∈ Subgroup.centralizer {zP} ↔ (g : Equiv.Perm (Fin 2300)) ∈ locC := by
      intro g
      rw [hcentz, Subgroup.mem_subgroupOf]
    have hN'C : N.map co2P.subtype ≤ locC := by
      rintro _ ⟨n, hn, rfl⟩
      exact (hmemC n).1 (hN1 hn)
    have hN'n : ∀ c ∈ locC, ∀ n ∈ N.map co2P.subtype, c * n * c⁻¹ ∈ N.map co2P.subtype := by
      rintro c hc _ ⟨n, hn, rfl⟩
      have hcP : c ∈ co2P := locC_le_P hc
      have := hN2 ⟨c, hcP⟩ ((hmemC ⟨c, hcP⟩).2 hc) n hn
      exact ⟨_, this, rfl⟩
    rcases Co2.locC_normal_le_or_eq hN'C hN'n with h | h
    · left
      intro n hn
      exact Subgroup.mem_subgroupOf.2 (h ⟨n, hn, rfl⟩)
    · right
      refine le_antisymm hN1 fun g hg => ?_
      have : (g : Equiv.Perm (Fin 2300)) ∈ N.map co2P.subtype := by
        rw [h]
        exact (hmemC g).1 hg
      obtain ⟨n, hn, hng⟩ := this
      have : n = g := Subtype.ext hng
      rw [← this]
      exact hn
  · intro B hBQ hcomm hsq
    have hB'Q : B.map co2P.subtype ≤ locQ := by
      rintro _ ⟨b, hb, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hBQ hb)
    have hcomm' : ∀ x ∈ B.map co2P.subtype, ∀ y ∈ B.map co2P.subtype, x * y = y * x := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hcomm x hx y hy)
    have h := Co2.locQ_abelian_le hB'Q hcomm'
    rw [Subgroup.card_map_of_injective co2P.subtype_injective] at h
    calc Nat.card B ≤ 32 := h
      _ = 2 ^ 5 := by norm_num
  · intro B hcomm hsq hno
    obtain ⟨T, hT, hTc⟩ := @exists_subgroup_map co2P NativeSporadic.Co2 _ Units.instGroup
      co2PermEquiv.symm B
    have hcard := Co2D5.d5_native T ?_ ?_ ?_
    · rw [hTc] at hcard
      calc Nat.card B ≤ 128 := hcard
        _ = 2 ^ 7 := by norm_num
    · intro x hx y hy
      obtain ⟨x', hx', rfl⟩ := (hT x).1 hx
      obtain ⟨y', hy', rfl⟩ := (hT y).1 hy
      rw [← map_mul, ← map_mul, hcomm x' hx' y' hy']
    · intro x hx
      obtain ⟨x', hx', rfl⟩ := (hT x).1 hx
      rw [← map_mul, hsq x' hx', map_one]
    · intro y hy hy1 hconj
      obtain ⟨b, hb, rfl⟩ := (hT y).1 hy
      refine hno b hb (fun h => hy1 (by rw [h, map_one])) ?_
      obtain ⟨c, hc⟩ := isConj_iff.1 ((isConj_symm_myRep (r := 0) (by norm_num)).trans hconj.symm)
      refine isConj_iff.2 ⟨co2PermEquiv c, ?_⟩
      have := congrArg co2PermEquiv hc
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      exact this
  · intro t ht2 ht1 hnc
    have ho : orderOf t = 2 := (orderOf_eq_two_iff_sq t).2 ⟨ht2, ht1⟩
    rcases isConj_cases_myRep t ho with h | h | h
    · exact absurd h.symm hnc
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · exact heis_sub (p := 3) (n := 1) locZ_mem Co2.heisA_ambient
  · exact heis_sub (p := 5) (n := 0) locT_mem Co2.heisB_ambient
  · exact heis_sub (p := 5) (n := 0) locU_mem Co2.heisC_ambient

theorem co2P_autInner :
    ∀ φ : co2P ≃* co2P, ∃ s : co2P, ∀ x, φ x = s * x * s⁻¹ := by
  intro φ
  obtain ⟨g, hg⟩ := CTUC_Co2_full_automorphisms_inner φ
  exact ⟨g, fun x => by rw [hg, MulAut.conj_apply]⟩

end Model

theorem co2P_hZ :
    ∀ (L : Type) [Group L] [Finite L], Group.IsPerfect L →
      Nonempty (L ⧸ Subgroup.center L ≃* co2P) → Nat.card (Subgroup.center L) = 1 := by
  intro L _ _ hperf ⟨e⟩
  let e' : L ⧸ Subgroup.center L ≃* NativeSporadic.Co2 := e.trans co2PermEquiv.symm
  have h3 : Nat.card (Subgroup.center L) ∣ 3 :=
    CFSG.Sporadic.Recognition.Co2Multiplier.card_center_dvd_three_of_certificate hperf e'
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Group.IsPerfect L := hperf
  have hnd : ¬ 3 ∣ Nat.card (Subgroup.center L) :=
    not_dvd_card_center_of_kernelTrivial
      CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.kernelTrivialAt_three_Co2 e'
  rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
  · exact h
  · exact absurd (by rw [h]) hnd

theorem noIrrFFOffender_co2P :
    NoIrrFFOffender co2P := by
  obtain ⟨D⟩ := co2CutData_nonempty
  exact noIrrFFOffender_of_co2CutData D co2P_autInner co2P_hZ

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Co2Model

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic

open CFSG.HardMathSupport.Cooperstein.Coordinator CFSG.Sporadic.Co2Cert

theorem noIrrFFOffender_Co2 :
    NoIrrFFOffender (TauCeti.CFSGIndex.sporadic .Co2).Group := by
  intro W _ _ hW L E hq hirr ⟨e⟩ hEN hE hel hquad
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  exact Co2Model.noIrrFFOffender_co2P W hW L E hq hirr ⟨e.trans (f.symm.trans co2PermEquiv)⟩
    hEN hE hel hquad

theorem gf2NoFFSporadicFor_Co2 :
    GF2NoFFSporadicFor .Co2 :=
  gf2NoFFSporadicFor_of_noIrrFFOffender noIrrFFOffender_Co2

end CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
