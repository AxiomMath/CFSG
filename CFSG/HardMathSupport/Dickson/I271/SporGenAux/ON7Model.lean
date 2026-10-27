module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Wrap
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7.SevenCent
public import Certificates.Certificate17390

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.ON.Native
  CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.KF148ONA7 CFSG.RankThree.PartTwo.Sec4

theorem primePowOK_seven_1372 : PrimePowOK 7 1372 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {2, 7})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

theorem primePowOK_seven_49 : PrimePowOK 7 49 := by
  refine primePow_mod_ne_one_of_check (by norm_num) (L := {7})
    (by norm_num [Nat.primeFactors]) ?_
  decide +kernel

section Records


@[expose] def on7R (r : Fin 3) : Fin 5 := Fin.castLE (by norm_num) r

@[expose] noncomputable def on7W (r : Fin 3) : Pv :=
  ⟨onSevenLine (onSevenRep (on7R r)), onSeven_mem_P.2.1 _⟩

@[expose] noncomputable def on7F (r : Fin 3) : Subgroup Pv := (onSevenF r).subgroupOf Pv

theorem on7W_ne_one (r : Fin 3) : on7W r ≠ 1 := fun h =>
  onSevenLine_ne_one (onSevenRep (on7R r)) (congrArg Subtype.val h)

theorem on7W_pow_seven (r : Fin 3) : on7W r ^ 7 = 1 :=
  Subtype.ext (by simpa [on7W] using onSevenLine_pow_seven (onSevenRep (on7R r)))

theorem orderOf_on7W (r : Fin 3) : orderOf (on7W r) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime (on7W_pow_seven r) (on7W_ne_one r)

theorem mem_centralizer_on7W_iff (r : Fin 3) {c : Pv} :
    c ∈ Subgroup.centralizer ({on7W r} : Set Pv) ↔
      (c : Equiv.Perm (Fin N)) ∈ onSevenC (on7R r) := by
  rw [onSevenC_eq (on7R r), Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨congrArg Subtype.val h, c.2⟩
  · rintro ⟨h, -⟩
    exact Subtype.ext h

theorem card_centralizer_on7W (r : Fin 3) :
    Nat.card (Subgroup.centralizer ({on7W r} : Set Pv)) = 7 ^ 3 * 4 := by
  rw [card_centralizer_subgroup_eq Pv (on7W r)]
  have h1 : (Subgroup.centralizer ({(on7W r : Equiv.Perm (Fin N))} : Set (Equiv.Perm (Fin N))) ⊓
      Pv) = onSevenC (on7R r) := (onSevenC_eq (on7R r)).symm
  have h2 : Nat.card (onSevenC (on7R r)) = 1372 := card_onSevenC_low r
  rw [h1, h2]
  norm_num

theorem on7_sevenLine (r : Fin 3) : SevenLine 7 (on7W r) (on7F r) := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨hFC, hFn, hFcard, hFcent, hxF⟩ := onSevenF_facts r
  have hFP : onSevenF r ≤ Pv := onSeven_mem_P.2.2.2.1 r
  refine sevenLine_of_data (m := 4) (on7W_ne_one r) (on7W_pow_seven r) ?_ (card_centralizer_on7W r)
    (by norm_num) ?_ ?_ ?_ ?_
  · exact Subgroup.mem_subgroupOf.2 hxF
  · intro f hf
    rw [mem_centralizer_on7W_iff]
    exact hFC (Subgroup.mem_subgroupOf.1 hf)
  · rw [on7F, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFP).toEquiv, hFcard]
    norm_num
  · intro c hc f hf
    rw [mem_centralizer_on7W_iff] at hc
    have := hFn.conj_mem ⟨f, hFC (Subgroup.mem_subgroupOf.1 hf)⟩ (Subgroup.mem_subgroupOf.2
      (Subgroup.mem_subgroupOf.1 hf)) ⟨c, hc⟩
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 this)
  · intro c hc hcf
    rw [mem_centralizer_on7W_iff] at hc
    have hmem : (c : Equiv.Perm (Fin N)) ∈
        Subgroup.centralizer (onSevenF r : Set (Equiv.Perm (Fin N))) ⊓ onSevenC (on7R r) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun g hg => ?_, hc⟩
      have := hcf ⟨g, hFP hg⟩ (Subgroup.mem_subgroupOf.2 hg)
      exact (congrArg Subtype.val this).symm
    have hmem2 : (c : Equiv.Perm (Fin N)) ∈
        Subgroup.zpowers (onSevenLine (onSevenRep (on7R r))) :=
      (congrArg (fun K => (c : Equiv.Perm (Fin N)) ∈ K) hFcent).mp hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem2
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa [on7W] using hn)⟩


theorem on7F0_sylow : ∃ S : Sylow 7 Pv, (S : Subgroup Pv) = on7F 0 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hcard : Nat.card (on7F 0) = 7 ^ (Nat.card Pv).factorization 7 := by
    rw [(on7_sevenLine 0).card_eq, factorization_card_Pv_seven]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem onSevenQ_le_C0 : onSevenQ ≤ onSevenC (on7R 0) := by
  refine (Subgroup.closure_le _).2 ?_
  intro y hy
  obtain ⟨k, hk, rfl⟩ := mem_evalList_iff.1 hy
  have hk2 : k < 2 := by simpa [onSevenSylowWords] using hk
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  · exact Subgroup.subset_closure (mem_evalList_iff.2 ⟨0, by decide, rfl⟩)
  · exact Subgroup.subset_closure (mem_evalList_iff.2 ⟨1, by decide, rfl⟩)

theorem on7_Q_comm : ∀ g ∈ onSevenQ,
    g * (on7W 0 : Equiv.Perm (Fin N)) = (on7W 0 : Equiv.Perm (Fin N)) * g := by
  intro g hg
  have hc := (mem_centralizer_on7W_iff 0 (c := ⟨g, onSeven_mem_P.1 hg⟩)).2 (onSevenQ_le_C0 hg)
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hc)

theorem onSevenQ_le_F0 : onSevenQ ≤ onSevenF 0 := by
  intro g hg
  have hc : (⟨g, onSeven_mem_P.1 hg⟩ : Pv) ∈ Subgroup.centralizer ({on7W 0} : Set Pv) := by
    rw [mem_centralizer_on7W_iff, onSevenC_eq (on7R 0)]
    exact Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (on7_Q_comm g hg),
      onSeven_mem_P.1 hg⟩
  have h7 : (⟨g, onSeven_mem_P.1 hg⟩ : Pv) ^ 7 = 1 :=
    Subtype.ext (by simpa using onSevenQ_pow_seven hg)
  have := (on7_sevenLine 0).syl _ hc ⟨1, by rw [pow_one]; exact h7⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem on7W_mem_F0 (r : Fin 3) : on7W r ∈ on7F 0 :=
  Subgroup.mem_subgroupOf.2 (onSevenQ_le_F0 (onSevenLine_mem_Q _))

theorem on7W_not_mem_zpowers (r : Fin 3) (hr : r ≠ 0) :
    on7W r ∉ Subgroup.zpowers (on7W 0) := by
  intro h
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hP : (on7W r : Equiv.Perm (Fin N)) ∈
      Subgroup.zpowers (on7W 0 : Equiv.Perm (Fin N)) := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 h
    exact Subgroup.mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hle : Subgroup.zpowers (onSevenLine (onSevenRep (on7R r))) ≤
      Subgroup.zpowers (onSevenLine (onSevenRep (on7R 0))) := Subgroup.zpowers_le.2 hP
  have heq : Subgroup.zpowers (onSevenLine (onSevenRep (on7R r))) =
      Subgroup.zpowers (onSevenLine (onSevenRep (on7R 0))) := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_onSevenLine, orderOf_onSevenLine]
  have hinj := onSevenQ_lines.2 heq
  fin_cases r
  · exact hr rfl
  · exact absurd hinj (by decide)
  · exact absurd hinj (by decide)


@[expose] def on7PermSet : Set (Equiv.Perm (Fin N)) :=
  {g | ∃ r : Fin 3, g ∈ evalList onSevenCentWords[(on7R r : ℕ)]!}

@[expose] def on7GenSet : Set Pv := {x | (x : Equiv.Perm (Fin N)) ∈ on7PermSet}

theorem on7PermSet_mem {g : Equiv.Perm (Fin N)} (hg : g ∈ on7PermSet) : g ∈ Pv := by
  obtain ⟨r, hr⟩ := hg
  exact evalList_mem hr

theorem on7_gens_top : Subgroup.closure on7GenSet = ⊤ := by
  have hPv : Pv ≤ Subgroup.closure on7PermSet := Certificates.certificate17390.ge
  have key : ∀ v (hv : v ∈ Subgroup.closure on7PermSet),
      ∃ hP : v ∈ Pv, (⟨v, hP⟩ : Pv) ∈ Subgroup.closure on7GenSet := by
    intro v hv
    induction hv using Subgroup.closure_induction with
    | mem y hy => exact ⟨on7PermSet_mem hy, Subgroup.subset_closure hy⟩
    | one => exact ⟨Pv.one_mem, one_mem _⟩
    | mul y z _ _ hy hz => exact ⟨Pv.mul_mem hy.1 hz.1, mul_mem hy.2 hz.2⟩
    | inv y _ hy => exact ⟨Pv.inv_mem hy.1, inv_mem hy.2⟩
  rw [eq_top_iff]
  intro x _
  exact (key _ (hPv x.2)).2

theorem on7_rankOK : ∀ e : Pv, orderOf e = 7 → RankOK 7 (Subgroup.centralizer ({e} : Set Pv)) := by
  intro e he
  refine rankOK_of_primePowOK ?_
  rcases card_centralizer_seven_Pv he with h | h
  · rw [h]; exact primePowOK_seven_1372
  · rw [h]; exact primePowOK_seven_49

theorem on7_sevenModel :
    SevenModel Pv 7 (on7F 0) (on7W 0) on7GenSet where
  line := on7_sevenLine 0
  syl := on7F0_sylow
  gens_top := on7_gens_top
  gens_good := by
    rintro g ⟨r, hr⟩
    have hgC : g ∈ Subgroup.centralizer ({on7W r} : Set Pv) := by
      rw [mem_centralizer_on7W_iff]
      exact Subgroup.subset_closure hr
    by_cases hr0 : r = 0
    · subst hr0
      exact Or.inl hgC
    · exact Or.inr (Or.inl ⟨on7W r, on7F r, on7_sevenLine r, on7W_mem_F0 r,
        on7W_not_mem_zpowers r hr0, hgC⟩)
  rankOK := on7_rankOK

end Records

open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census

theorem sporPlaneKill_ONan_seven
    (hOut : SporadicOuterLeTwo) : SporPlaneKill .ONan 7 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  have b₀ : NativeSporadic.Carrier .ONan ≃* Spor .ONan := b
  have bX : ↥Pv ≃* Spor .ONan := onEquivPv.symm.trans b₀
  exact sporPlaneKill_of_sevenModel hOut (by decide) bX ⟨_, _, _, on7_sevenModel⟩ b₀ offPair_ONan

theorem sporPair_ONan_seven
    (hOut : SporadicOuterLeTwo) : SporPair .ONan 7 :=
  sporPair_of_planeKill (sporPlaneKill_ONan_seven hOut)

end CFSG.HardMathSupport.Dickson.I271
