module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsSetup
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U38K0
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.RankThree.PartTwo.Sec16.Item166Res8ProofComm

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open Subgroup

theorem u38R_normalizer_le_centralizer {H : Type} [Group H] [Finite H] {z : H}
    (hz : z ∈ Subgroup.center H) (hzo : orderOf z = 3) (P : Sylow 3 H)
    (hPc : IsCyclic (P : Subgroup H)) (hzP : z ∈ (P : Subgroup H)) :
    Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ a ∈ (P : Subgroup H), ∀ b ∈ (P : Subgroup H), a * b = b * a := by
    intro a ha b hb
    letI : CommGroup (P : Subgroup H) := IsCyclic.commGroup
    exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : (P : Subgroup H)) ⟨b, hb⟩)
  intro n hn
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos n).ne' 3
    (by norm_num)
  have hh : n ^ b ∈ (P : Subgroup H) := by
    have hord : (n ^ b) ^ 3 ^ a = 1 := by
      rw [← pow_mul, mul_comm b, ← hab, pow_orderOf_eq_one]
    have hzp : IsPGroup 3 (zpowers (n ^ b)) := by
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (orderOf_dvd_of_pow_eq_one hord)
      exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
    have hle : zpowers (n ^ b) ≤ Subgroup.normalizer (P : Set H) :=
      (zpowers_le).mpr (pow_mem hn b)
    have h1 := P.is_maximal' (IsPGroup.to_sup_of_normal_left' P.isPGroup' hzp hle) le_sup_left
    have h2 : n ^ b ∈ (P : Subgroup H) ⊔ zpowers (n ^ b) := mem_sup_right (mem_zpowers _)
    rwa [h1] at h2
  have hcop : Nat.Coprime b 3 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hb).symm
  have hcent : n ^ 3 ^ a ∈ Subgroup.centralizer (P : Set H) := by
    refine CFSG.RankThree.PartTwo.Sec17.Proof168Res8Comm.mem_centralizer_of_coprime hPc
      P.isPGroup' hzP hzo (pow_mem hn _) ?_ ?_
    · have hdv : orderOf (n ^ 3 ^ a) ∣ b := by
        rw [orderOf_dvd_iff_pow_eq_one, ← pow_mul, ← hab, pow_orderOf_eq_one]
      exact Nat.Coprime.coprime_dvd_left hdv hcop
    · rw [Subgroup.mem_center_iff] at hz
      rw [hz (n ^ 3 ^ a), mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨x, y, hxy⟩ : IsCoprime (b : ℤ) ((3 : ℤ) ^ a) := by
    have h := Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_right a hcop)
    exact_mod_cast h
  have hsplit : n = (n ^ b) ^ x * (n ^ 3 ^ a) ^ y := by
    have e1 : (n ^ b) ^ x = n ^ ((b : ℤ) * x) := by
      rw [← zpow_natCast n b, ← zpow_mul]
    have e2 : (n ^ 3 ^ a) ^ y = n ^ (((3 : ℤ) ^ a) * y) := by
      rw [← zpow_natCast n (3 ^ a), ← zpow_mul]
      push_cast
      rfl
    rw [e1, e2, ← zpow_add]
    have h1 : (b : ℤ) * x + ((3 : ℤ) ^ a) * y = 1 := by linarith
    rw [h1, zpow_one]
  rw [hsplit]
  have hA : (n ^ b) ^ x ∈ (P : Subgroup H) := zpow_mem hh x
  have hB : (n ^ 3 ^ a) ^ y ∈ Subgroup.centralizer (P : Set H) := zpow_mem hcent y
  rw [Subgroup.mem_centralizer_iff] at hB ⊢
  intro g hg
  have hA' : g * (n ^ b) ^ x = (n ^ b) ^ x * g := hcomm g hg _ hA
  have hB' : g * (n ^ 3 ^ a) ^ y = (n ^ 3 ^ a) ^ y * g := hB g hg
  rw [← mul_assoc, hA', mul_assoc, hB', ← mul_assoc]

theorem u38R_exists_normal_compl {H : Type} [Group H] [Finite H] {z : H}
    (hz : z ∈ Subgroup.center H) (hzo : orderOf z = 3)
    (hcyc : ∀ S : Subgroup H, IsPGroup 3 S → IsCyclic S)
    (T : Subgroup H) (hT : IsPGroup 2 T) :
    ∃ M : Subgroup H, M.Normal ∧ ¬ 3 ∣ Nat.card M ∧ T ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  have hPc : IsCyclic (P : Subgroup H) := hcyc _ P.isPGroup'
  have hzN : (zpowers z).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hn
    have hc : g * z = z * g := Subgroup.mem_center_iff.1 hz g
    rw [(Commute.zpow_right (show Commute g z from hc) k).eq, mul_assoc, mul_inv_cancel, mul_one]
    exact zpow_mem (mem_zpowers z) k
  have hzP : z ∈ (P : Subgroup H) := by
    have hp : IsPGroup 3 ↥(zpowers z) :=
      IsPGroup.of_card (n := 1) (show Nat.card (zpowers z) = 3 ^ 1 by rw [Nat.card_zpowers, hzo, pow_one])
    exact (IsPGroup.le_sylow_of_normal hp P) (mem_zpowers z)
  have hN := u38R_normalizer_le_centralizer hz hzo P hPc hzP
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hN
  refine ⟨(MonoidHom.transferSylow P hN).ker, inferInstance,
    MonoidHom.not_dvd_card_ker_transferSylow P hN, ?_⟩
  obtain ⟨j, hj⟩ := P.isPGroup'.exists_card_eq
  have hM : (MonoidHom.transferSylow P hN).ker.index = 3 ^ j := hcomp.symm.index_eq_card.trans hj
  intro t ht
  obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
  have hk' : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  set M := (MonoidHom.transferSylow P hN).ker with hMdef
  have h2 : orderOf (QuotientGroup.mk' M t) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow, hk', map_one]
  have h3 : orderOf (QuotientGroup.mk' M t) ∣ 3 ^ j := by
    rw [← hM]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime (2 ^ k) (3 ^ j) := Nat.Coprime.pow _ _ (by norm_num)
  have h4 : orderOf (QuotientGroup.mk' M t) = 1 := by
    have := Nat.dvd_gcd h2 h3
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    exact Nat.dvd_one.1 this
  rw [orderOf_eq_one_iff] at h4
  exact (QuotientGroup.eq_one_iff t).1 h4

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

noncomputable def u38R_act {G : Type} [Group G] (L : Subgroup G) {S : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (L : Set G)) : ↥S →* MulAut (PSimple 3 L) :=
  (chevAut 3 L).comp (Subgroup.inclusion hS)

theorem u38R_act_eq_one_iff {G : Type} [Group G] [Finite G] {L C : Subgroup G}
    (hL : GLAPComponent 3 C L) (hCN : C ≤ Subgroup.normalizer (L : Set G))
    {S : Subgroup G} (hS : S ≤ C) (s : G) (hs : s ∈ S) :
    u38R_act L (hS.trans hCN) ⟨s, hs⟩ = 1 ↔ s ∈ centModSubgroup 3 L :=
  (chevAut_eq_one_iff Nat.prime_three hL (hCN (hS hs))).trans centMod_iff

theorem u38R_chev_conj {G : Type} [Group G] (L : Subgroup G) (a b : G)
    (ha : a ∈ Subgroup.normalizer (L : Set G)) (hb : b ∈ Subgroup.normalizer (L : Set G))
    (hab : a * b * a⁻¹ ∈ Subgroup.normalizer (L : Set G)) :
    chevAut 3 L ⟨a * b * a⁻¹, hab⟩ =
      chevAut 3 L ⟨a, ha⟩ * chevAut 3 L ⟨b, hb⟩ * (chevAut 3 L ⟨a, ha⟩)⁻¹ := by
  have h : (⟨a * b * a⁻¹, hab⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      ⟨a, ha⟩ * ⟨b, hb⟩ * (⟨a, ha⟩)⁻¹ := by
    apply Subtype.ext
    simp [mul_assoc]
  rw [h, map_mul, map_mul, map_inv]



theorem u38R_card_range_dvd {G H : Type} [Group G] [Group H] [Finite G] (f : G →* H) :
    Nat.card ↥f.range ∣ Nat.card G := by
  have := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at this
  exact Dvd.intro_left _ this

section Row


theorem u38RankAt_holds (G : Type) [Group G] [Finite G] : U38RankAt G := by
  intro x L hx hL hcat hcyc hlayer E T hEC hEab hTC hT2 hEN hTnot
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hCN : C ≤ Subgroup.normalizer (L : Set G) := by
    have h := CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.le_normalizer_gLAPLayer 3
      (B := C) (X := C) Subgroup.le_normalizer
    rwa [hlayer] at h
  set K₀ : Subgroup G := C ⊓ centModSubgroup 3 L with hK₀def
  have hK₀mem : ∀ g, g ∈ K₀ ↔ g ∈ C ∧ g ∈ centModSubgroup 3 L := fun g => Subgroup.mem_inf
  have hK₀C : K₀ ≤ C := inf_le_left
  have hK₀conj : ∀ c ∈ C, ∀ n ∈ K₀, c * n * c⁻¹ ∈ K₀ := by
    intro c hc n hn
    obtain ⟨hnC, hnM⟩ := (hK₀mem n).1 hn
    refine (hK₀mem _).2 ⟨C.mul_mem (C.mul_mem hc hnC) (C.inv_mem hc), ?_⟩
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := hCN hc
    rw [mem_centModSubgroup] at hnM ⊢
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hcN hnM.1) (Subgroup.inv_mem _ hcN),
      fun l hl => ?_⟩
    have hcl : c⁻¹ * l * c ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hcN) l).1 hl
      simpa using this
    have h1 : ⁅c⁻¹ * l * c, n⁆ ∈ GLAPPrimeCoreOf 3 L := hnM.2 _ hcl
    have h2 : c * ⁅c⁻¹ * l * c, n⁆ * c⁻¹ ∈ GLAPPrimeCoreOf 3 L :=
      (Subgroup.mem_normalizer_iff.1 (normalizer_le_normalizer_glaPPrimeCoreOf 3 L hcN) _).1 h1
    have heq : ⁅l, c * n * c⁻¹⁆ = c * ⁅c⁻¹ * l * c, n⁆ * c⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact h2
  have hK₀normal : (K₀.subgroupOf C).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hK₀conj g.1 g.2 n hn
    simpa using this
  have hxK₀ : x ∈ K₀ := by
    refine (hK₀mem x).2 ⟨hxC, ?_⟩
    rw [mem_centModSubgroup]
    refine ⟨hCN hxC, fun l hl => ?_⟩
    have hlC : l ∈ C := hL.1 hl
    have hcomm : l * x = x * l := Subgroup.mem_centralizer_singleton_iff.1 hlC
    have h1 : ⁅l, x⁆ = 1 := by
      rw [commutatorElement_def, hcomm]
      group
    rw [h1]
    exact Subgroup.one_mem _
  set z : K₀ := ⟨x, hxK₀⟩ with hzdef
  have hzcent : z ∈ Subgroup.center K₀ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hg : (g : G) * x = x * (g : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 ((hK₀mem g.1).1 g.2).1
    simp only [Subgroup.coe_mul]
    exact hg
  have hzo : orderOf z = 3 := by
    rw [hzdef, Subgroup.orderOf_mk]
    exact hx
  have hcycK : ∀ S : Subgroup K₀, IsPGroup 3 S → IsCyclic S := by
    intro S hS
    have hS' : IsPGroup 3 ↥(S.map K₀.subtype) := hS.map K₀.subtype
    have hc : IsCyclic ↥(S.map K₀.subtype) := by
      refine hcyc (S.map K₀.subtype) ?_ hS'
      intro g hg
      obtain ⟨s, -, rfl⟩ := Subgroup.mem_map.1 hg
      exact centMod_iff.2 ((hK₀mem s.1).1 s.2).2
    exact (MulEquiv.isCyclic
      (Subgroup.equivMapOfInjective S K₀.subtype K₀.subtype_injective)).2 hc
  have hTK : ¬ T ≤ K₀ := by
    intro hTK
    have hT2K : IsPGroup 2 ↥(T.subgroupOf K₀) := by
      intro g
      obtain ⟨n, hn⟩ := hT2 ⟨g.1.1, Subgroup.mem_subgroupOf.1 g.2⟩
      refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
      have := congrArg Subtype.val hn
      simpa using this
    obtain ⟨M, hMn, hM3, hTM⟩ :=
      u38R_exists_normal_compl hzcent hzo hcycK (T.subgroupOf K₀) hT2K
    apply hTnot
    have hMcop : Nat.Coprime 3 (Nat.card M) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hM3
    have hMle : M.map K₀.subtype ≤ GLAPPrimeCoreOf 3 K₀ := by
      intro y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hy
      have hMP : M ≤ CFSG.pPrimeCore 3 ↥K₀ := le_sSup ⟨hMn, hMcop⟩
      have hm' : m ∈ CFSG.pPrimeCore 3 ↥K₀ := hMP hm
      show K₀.subtype m ∈ (GLAPPrimeCore 3 ↥K₀).map K₀.subtype
      exact Subgroup.mem_map.2 ⟨m, hm', rfl⟩
    have hTK₀ : T ≤ GLAPPrimeCoreOf 3 K₀ := by
      intro t ht
      have htK : t ∈ K₀ := hTK ht
      have hmem : (⟨t, htK⟩ : ↥K₀) ∈ T.subgroupOf K₀ := Subgroup.mem_subgroupOf.2 ht
      have hmapt : t ∈ M.map K₀.subtype := Subgroup.mem_map.2 ⟨⟨t, htK⟩, hTM hmem, rfl⟩
      exact hMle hmapt
    exact hTK₀.trans (glaPPrimeCoreOf_le_of_normal Nat.prime_three hK₀C hK₀normal)
  obtain ⟨t₀, ht₀T, ht₀K⟩ : ∃ t ∈ T, t ∉ K₀ := by
    by_contra hcon
    exact hTK (fun t ht => by
      by_contra h
      exact hcon ⟨t, ht, h⟩)
  set ψE := u38R_act L (hEC.trans hCN) with hψEdef
  set ψT := u38R_act L (hTC.trans hCN) with hψTdef
  have hψT_ne : ψT ⟨t₀, ht₀T⟩ ≠ 1 := fun h =>
    ht₀K ((hK₀mem t₀).2 ⟨hTC ht₀T, (u38R_act_eq_one_iff hL hCN hTC t₀ ht₀T).1 h⟩)
  have hkerE : Nat.card ↥ψE.ker ≤ 3 := by
    set S : Subgroup G := ψE.ker.map E.subtype with hSdef
    have hcardS : Nat.card ↥ψE.ker = Nat.card ↥S :=
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective E)).symm
    have hSE : S ≤ E := by
      intro g hg
      obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hg
      exact k.2
    have hSp : IsPGroup 3 ↥S := (isPGroup_of_isElemAbelian hEab).to_le hSE
    have hSc : IsCyclic ↥S := by
      refine hcyc S ?_ hSp
      intro g hg
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hg
      exact centMod_iff.2 ((u38R_act_eq_one_iff hL hCN hEC k.1 k.2).1 (MonoidHom.mem_ker.1 hk))
    obtain ⟨gen, hgen⟩ := IsCyclic.exists_generator (α := ↥S)
    have hg3 : gen ^ 3 = 1 := by
      apply Subtype.ext
      have := hEab.2 (gen : G) (hSE gen.2)
      simpa using this
    have hord : orderOf gen = Nat.card ↥S := orderOf_eq_card_of_forall_mem_zpowers hgen
    have hdvd : orderOf gen ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have hle : Nat.card ↥S ≤ 3 := by
      rw [← hord]
      exact Nat.le_of_dvd (by norm_num) hdvd
    rw [hcardS]
    exact hle
  have hcardE : Nat.card ↥E = Nat.card ↥ψE.ker * Nat.card ↥ψE.range := by
    have := Subgroup.card_mul_index ψE.ker
    rw [Subgroup.index_ker] at this
    exact this.symm
  have hconj : ∀ e : ↥E, ∀ w ∈ ψT.range, ψE e * w * (ψE e)⁻¹ ∈ ψT.range := by
    intro e w hw
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.1 hw
    have heN : (e : G) ∈ Subgroup.normalizer (L : Set G) := hCN (hEC e.2)
    have hetT : (e : G) * (t : G) * (e : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.1 (hEN e.2) t).1 t.2
    have hetN : (e : G) * (t : G) * (e : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
      hCN (hTC hetT)
    have key := u38R_chev_conj L (e : G) (t : G) heN (hCN (hTC t.2)) hetN
    exact MonoidHom.mem_range.2 ⟨⟨(e : G) * (t : G) * (e : G)⁻¹, hetT⟩, key⟩
  have hEcomm : ∀ a b : ↥E, a * b = b * a := fun a b => hEab.1.is_comm.comm a b
  have hX : Nonempty (PSimple 3 L ≃* ↥(CFSG.PGLModel.projSU 3 2 3)) := by
    obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.bridge_u3eight hcat
    have hP : CFSG.PGLModel.projImage (CFSG.Open.StatedSU 3 (2 ^ 3) (GaloisField 2 6)) =
        CFSG.PGLModel.projSU 3 2 3 :=
      CFSG.RankThree.PartOne.projImage_statedSU_eq_projSU 3 2 3
    exact ⟨e.trans (CFSG.Adapters.RankTwoModelTransports.statedProjEquivProjImage _ hP)⟩
  have hYdvd : ¬ 3 ∣ Nat.card ↥ψT.range := by
    intro h3
    obtain ⟨m, hm⟩ := hT2.exists_card_eq
    have h1 : Nat.card ↥ψT.range ∣ Nat.card ↥T := u38R_card_range_dvd ψT
    rw [hm] at h1
    have h2 : 3 ∣ 2 ^ m := h3.trans h1
    have h4 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
    omega
  have hrange : Nat.card ↥ψE.range ≤ 9 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hEab).exists_card_eq
    have hdvd : Nat.card ↥ψE.range ∣ 3 ^ n := hn ▸ u38R_card_range_dvd ψE
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hdvd
    have hj3 : 3 ≤ j := by
      by_contra h
      push_neg at h
      interval_cases j <;> (rw [hjeq] at hgt; norm_num at hgt)
    have h27 : 3 ^ 3 ∣ Nat.card ↥ψE.range := by
      rw [hjeq]
      exact pow_dvd_pow 3 hj3
    obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 3 h27
    set F : Subgroup (MulAut (PSimple 3 L)) := K'.map ψE.range.subtype with hFdef
    have hF27 : Nat.card ↥F = 27 := by
      rw [hFdef, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK']
      norm_num
    have hFelem : ∀ f ∈ F, ∃ e : ↥E, ψE e = f := by
      intro f hf
      obtain ⟨k, -, rfl⟩ := Subgroup.mem_map.1 hf
      obtain ⟨e, he⟩ := MonoidHom.mem_range.1 k.2
      exact ⟨e, he⟩
    have hcommR : ∀ f ∈ F, ∀ g ∈ F, f * g = g * f := by
      intro f hf g hg
      obtain ⟨e, rfl⟩ := hFelem f hf
      obtain ⟨e', rfl⟩ := hFelem g hg
      rw [← map_mul, ← map_mul, hEcomm e e']
    have hFab : CFSG.Open.IsElemAbelian 3 F := by
      refine ⟨⟨⟨fun a b => Subtype.ext (hcommR a.1 a.2 b.1 b.2)⟩⟩, fun f hf => ?_⟩
      obtain ⟨e, rfl⟩ := hFelem f hf
      rw [← map_pow]
      have h3 : e ^ 3 = 1 := Subtype.ext (by simpa using hEab.2 e.1 e.2)
      rw [h3, map_one]
    have hFN : F ≤ Subgroup.normalizer (ψT.range : Set (MulAut (PSimple 3 L))) := by
      intro f hf
      obtain ⟨e, rfl⟩ := hFelem f hf
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw
        exact hconj e w hw
      · intro hw
        have h := hconj e⁻¹ _ hw
        rw [map_inv] at h
        have key : (ψE e)⁻¹ * (ψE e * w * (ψE e)⁻¹) * (ψE e)⁻¹⁻¹ = w := by group
        rw [key] at h
        exact h
    have hYbot : ψT.range = ⊥ :=
      CFSG.RankThree.PartTwo.Sec4.Item434U38.u38K0 (PSimple 3 L) hX F hFab hF27 ψT.range
        hYdvd hFN
    have hmem : ψT ⟨t₀, ht₀T⟩ ∈ ψT.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
    rw [hYbot, Subgroup.mem_bot] at hmem
    exact hψT_ne hmem
  calc Nat.card ↥E = Nat.card ↥ψE.ker * Nat.card ↥ψE.range := hcardE
    _ ≤ 3 * 9 := Nat.mul_le_mul hkerE hrange
    _ = 3 ^ 3 := by norm_num

end Row

end CFSG.LocalAnalysis.GLTheoremA
