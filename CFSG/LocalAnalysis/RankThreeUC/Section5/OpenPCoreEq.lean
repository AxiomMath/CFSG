module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Wielandt
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Unfold
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

open scoped Pointwise

namespace OddActorSylowFactorization

theorem openPCore_eq (p : ℕ) (G : Type) [Group G] : CFSG.Open.pCore p G = CFSG.pCore p G := rfl

theorem odd_of_pCore_bot {Q : Type} [Group Q] [Finite Q] (hQ : CFSG.pCore 2 Q = ⊥)
    (F : Subgroup Q) [F.Normal] [Group.IsNilpotent F] : Odd (Nat.card F) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card F := by
    rcases Nat.even_or_odd (Nat.card F) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 h2
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx]; simp
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have h1 := Sylow.map_le_pCore (N := F) inferInstance inferInstance 2 P
  rw [hQ] at h1
  have hx' : (x : Q) ∈ P.map F.subtype := ⟨x, hP (Subgroup.mem_zpowers x), rfl⟩
  have := h1 hx'
  rw [Subgroup.mem_bot] at this
  have hx1 : x = 1 := Subtype.ext this
  rw [hx1, orderOf_one] at hx
  omega

variable {X : Type} [Group X] [Finite X]

theorem pCore_quot_bot : CFSG.pCore 2 (X ⧸ CFSG.pCore 2 X) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.pCore 2 X
  haveI : N.Normal := CFSG.pCore_normal
  set K := CFSG.pCore 2 (X ⧸ N)
  haveI : K.Normal := CFSG.pCore_normal
  have hK : IsPGroup 2 K := CFSG.pCore_isPGroup
  have hN : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hc : IsPGroup 2 (K.comap (QuotientGroup.mk' N)) := by
    exact hK.comap_of_ker_isPGroup (QuotientGroup.mk' N) (by rwa [QuotientGroup.ker_mk'])
  have hle : K.comap (QuotientGroup.mk' N) ≤ N := le_sSup ⟨inferInstance, hc⟩
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have : x ∈ N := hle hy
  simpa using (QuotientGroup.eq_one_iff x).mpr this

theorem solvable_of_sup {Bx Tx : Subgroup X}
    (hBab : ∀ a ∈ Bx, ∀ b ∈ Bx, a * b = b * a) (hBodd : Odd (Nat.card Bx)) (hT : IsPGroup 2 Tx)
    (hperm : (Bx : Set X) * Tx = Tx * Bx) (hsup : Bx ⊔ Tx = ⊤) : Group.IsSolvable X := by
  have h := isSolvable_sup_of_perm_odd_two hBab hBodd hT hperm
  rw [hsup] at h
  haveI := h
  exact solvable_of_solvable_injective (f := (Subgroup.topEquiv (G := X)).symm.toMonoidHom)
    (Subgroup.topEquiv (G := X)).symm.injective

theorem mem_sup_mul {Bx Tx : Subgroup X} (hperm : (Bx : Set X) * Tx = Tx * Bx) {x : X}
    (hx : x ∈ Bx ⊔ Tx) : ∃ b ∈ Bx, ∃ t ∈ Tx, x = b * t := by
  let S : Subgroup X :=
    { carrier := (Bx : Set X) * Tx
      one_mem' := ⟨1, Bx.one_mem, 1, Tx.one_mem, mul_one 1⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, t, ht, rfl⟩ ⟨b', hb', t', ht', rfl⟩
        have : t * b' ∈ (Tx : Set X) * Bx := ⟨t, ht, b', hb', rfl⟩
        rw [← hperm] at this
        obtain ⟨b'', hb'', t'', ht'', h⟩ := this
        refine ⟨b * b'', Bx.mul_mem hb hb'', t'' * t', Tx.mul_mem ht'' ht', ?_⟩
        calc b * b'' * (t'' * t') = b * (b'' * t'') * t' := by group
          _ = b * (t * b') * t' := by rw [show b'' * t'' = t * b' from h]
          _ = _ := by group
      inv_mem' := by
        rintro _ ⟨b, hb, t, ht, rfl⟩
        have : t⁻¹ * b⁻¹ ∈ (Tx : Set X) * Bx := ⟨t⁻¹, Tx.inv_mem ht, b⁻¹, Bx.inv_mem hb, rfl⟩
        rw [← hperm] at this
        obtain ⟨b'', hb'', t'', ht'', h⟩ := this
        exact ⟨b'', hb'', t'', ht'', by rw [h]; group⟩ }
  have hle : Bx ⊔ Tx ≤ S :=
    sup_le (fun b hb => ⟨b, hb, 1, Tx.one_mem, mul_one b⟩)
      (fun t ht => ⟨1, Bx.one_mem, t, ht, one_mul t⟩)
  obtain ⟨b, hb, t, ht, h⟩ := hle hx
  exact ⟨b, hb, t, ht, h.symm⟩

theorem fittingQuotient_eq_actor_image {Bx Tx : Subgroup X}
    (hBab : ∀ a ∈ Bx, ∀ b ∈ Bx, a * b = b * a) (hBodd : Odd (Nat.card Bx)) (hT : IsPGroup 2 Tx)
    (hperm : (Bx : Set X) * Tx = Tx * Bx) (hsup : Bx ⊔ Tx = ⊤) :
    Bx.map (QuotientGroup.mk' (CFSG.pCore 2 X)) = CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hXs : Group.IsSolvable X := solvable_of_sup hBab hBodd hT hperm hsup
  haveI hQs : Group.IsSolvable (X ⧸ CFSG.pCore 2 X) :=
    solvable_of_surjective (QuotientGroup.mk'_surjective (CFSG.pCore 2 X))
  obtain ⟨Bb, hBb⟩ : ∃ Bb, Bb = Bx.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := ⟨_, rfl⟩
  obtain ⟨Tb, hTb⟩ : ∃ Tb, Tb = Tx.map (QuotientGroup.mk' (CFSG.pCore 2 X)) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = CFSG.fittingSubgroup (X ⧸ CFSG.pCore 2 X) := ⟨_, rfl⟩
  rw [← hBb, ← hF]
  haveI : F.Normal := by rw [hF]; infer_instance
  haveI : Group.IsNilpotent F := by rw [hF]; infer_instance
  have hFodd : Odd (Nat.card F) := odd_of_pCore_bot pCore_quot_bot F
  have hBbodd : Odd (Nat.card Bb) :=
    by rw [hBb]; exact Odd.of_dvd_nat hBodd (Subgroup.card_map_dvd (H := Bx) (QuotientGroup.mk' (CFSG.pCore 2 X)))
  have hTbp : IsPGroup 2 Tb := by rw [hTb]; exact hT.map _
  have hBbab : ∀ a ∈ Bb, ∀ b ∈ Bb, a * b = b * a := by
    rw [hBb]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hBab a ha b hb]
  have hcop : Nat.Coprime (Nat.card Bb) (Nat.card Tb) := by
    obtain ⟨k, hk⟩ := hTbp.exists_card_eq
    rw [hk]; exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBbodd)
  have hdisj : Bb ⊓ Tb = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop
  have hmul : (Bb : Set (X ⧸ CFSG.pCore 2 X)) * (Tb : Set (X ⧸ CFSG.pCore 2 X)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ Bx ⊔ Tx := by rw [hsup]; trivial
    obtain ⟨b, hb, t, ht, rfl⟩ := mem_sup_mul hperm hx
    refine Set.mem_mul.mpr ⟨QuotientGroup.mk' (CFSG.pCore 2 X) b, ?_, QuotientGroup.mk' (CFSG.pCore 2 X) t, ?_, ?_⟩
    · rw [hBb]; exact ⟨b, hb, rfl⟩
    · rw [hTb]; exact ⟨t, ht, rfl⟩
    · simp
  have hcomp : Subgroup.IsComplement' Bb Tb :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj) hmul
  have hidx : Bb.index = Nat.card Tb := hcomp.symm.index_eq_card
  have hFle : F ≤ Bb := by
    set H := F ⊔ Bb with hH
    have hBH : Bb ≤ H := le_sup_right
    have hFH : F ≤ H := le_sup_left
    have h1 : F.relIndex H = F.relIndex Bb := by rw [hH]; exact Subgroup.relIndex_sup_left Bb F
    have h2 : Odd (F.relIndex H) := by
      rw [h1]; exact Odd.of_dvd_nat hBbodd (Subgroup.relIndex_dvd_card F Bb)
    have h3 : Odd (Nat.card H) := by
      have h6 := Subgroup.card_mul_index (H := F.subgroupOf H)
      have h7 : Nat.card (F.subgroupOf H) = Nat.card F :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv
      rw [h7] at h6
      have h8 : (F.subgroupOf H).index = F.relIndex H := rfl
      rw [h8] at h6
      rw [← h6]
      exact hFodd.mul h2
    have h4 : Bb.relIndex H ∣ Bb.index := Subgroup.relIndex_dvd_index_of_le hBH
    have h5 : Bb.relIndex H ∣ Nat.card H := Subgroup.relIndex_dvd_card Bb H
    have h9 : Bb.relIndex H ∣ Nat.card Tb := hidx ▸ h4
    obtain ⟨k, hk⟩ := hTbp.exists_card_eq
    rw [hk] at h9
    have h10 : Nat.Coprime (Bb.relIndex H) (2 ^ k) := by
      apply Nat.Coprime.pow_right
      exact Nat.coprime_two_right.mpr (Odd.of_dvd_nat h3 h5)
    have h11 : Bb.relIndex H = 1 := Nat.Coprime.eq_one_of_dvd h10 h9
    exact hFH.trans (Subgroup.relIndex_eq_one.mp h11)
  have hBF : Bb ≤ F := by
    have hcent : Bb ≤ Subgroup.centralizer (F : Set (X ⧸ CFSG.pCore 2 X)) := by
      intro b hb f hf
      exact (hBbab f (hFle hf) b hb)
    rw [hF] at hcent ⊢
    intro b hb
    exact CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hQs (hcent hb)
  exact le_antisymm hBF hFle

theorem hall_conj {N S Hh K : Subgroup X} [N.Normal] (hN : IsPGroup 2 N) (hNS : N ≤ S)
    (hHS : Hh ≤ S) (hKS : K ≤ S) (hH : Odd (Nat.card Hh)) (hK : Odd (Nat.card K))
    (hH' : ∀ s ∈ S, ∃ n ∈ N, ∃ h ∈ Hh, s = n * h) (hK' : ∀ s ∈ S, ∃ n ∈ N, ∃ h ∈ K, s = n * h) :
    ∃ n ∈ N, K = Hh.map (MulAut.conj n⁻¹).toMonoidHom := by
  have hN' : IsPGroup 2 (N.subgroupOf S) :=
    hN.comap_of_injective S.subtype Subtype.coe_injective
  haveI : Group.IsSolvable (N.subgroupOf S) := @IsNilpotent.to_isSolvable _ _ hN'.isNilpotent
  have key : ∀ (L : Subgroup X), L ≤ S → Odd (Nat.card L) →
      (∀ s ∈ S, ∃ n ∈ N, ∃ h ∈ L, s = n * h) →
      ((N.subgroupOf S : Subgroup S) : Set S) * ((L.subgroupOf S : Subgroup S) : Set S) = Set.univ ∧
      (N.subgroupOf S) ⊓ (L.subgroupOf S) = ⊥ := by
    intro L hLS hLodd hL'
    have hcardL : Nat.card (L.subgroupOf S) = Nat.card L :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLS).toEquiv
    constructor
    · apply Set.eq_univ_of_forall
      intro s
      obtain ⟨n, hn, h, hh, hs⟩ := hL' s.1 s.2
      exact Set.mem_mul.mpr ⟨⟨n, hNS hn⟩, Subgroup.mem_subgroupOf.mpr hn, ⟨h, hLS hh⟩,
        Subgroup.mem_subgroupOf.mpr hh, Subtype.ext hs.symm⟩
    · apply Subgroup.inf_eq_bot_of_coprime
      obtain ⟨k, hk⟩ := hN'.exists_card_eq
      rw [hk, hcardL]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hLodd)
  obtain ⟨h1, h2⟩ := key Hh hHS hH hH'
  obtain ⟨h3, h4⟩ := key K hKS hK hK'
  have hcompl : Subgroup.IsComplement' (N.subgroupOf S) (Hh.subgroupOf S) :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr h2) h1
  have hidx : (N.subgroupOf S).index = Nat.card Hh := by
    rw [hcompl.symm.index_eq_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHS).toEquiv
  have hcop : Nat.Coprime (Nat.card (N.subgroupOf S)) (N.subgroupOf S).index := by
    rw [hidx]
    obtain ⟨k, hk⟩ := hN'.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hH)
  obtain ⟨n, hn, hconj⟩ := CFSG.SolvableHall.solvable_normal_hall_complement_conjugacy
    (N.subgroupOf S) inferInstance hcop h1 h3 h2 h4
  refine ⟨(n : X), hn, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hKS hx⟩ : S) ∈ K.subgroupOf S := hx
    rw [hconj] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨(y : X), hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have hy' : (⟨y, hHS hy⟩ : S) ∈ Hh.subgroupOf S := hy
    have : (MulAut.conj n⁻¹).toMonoidHom ⟨y, hHS hy⟩ ∈ K.subgroupOf S := by
      rw [hconj]; exact ⟨_, hy', rfl⟩
    exact this

open CFSG in
theorem coprime_decomp {R A : Subgroup X} (hR : IsPGroup 2 R)
    (hA_norm_R : A ≤ Subgroup.normalizer (R : Set X)) (hAodd : Odd (Nat.card A)) :
    (R : Set X) =
      (⁅R, A⁆ : Subgroup X) *
        ((R ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
  let : Subgroup.Normalizes A R := ⟨hA_norm_R⟩
  let Cfix : Subgroup R := fixedPointSubgroup A R
  let Ccomm : Subgroup R := commutatorAction (A := A) (G := R)
  have hcop : Nat.Coprime (Nat.card A) (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hAodd)
  have hsolvR : Group.IsSolvable R := @IsNilpotent.to_isSolvable _ _ hR.isNilpotent
  have hsup : Cfix ⊔ Ccomm = ⊤ :=
    fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime hsolvR hcop
  have hcommMap : Ccomm.map R.subtype = ⁅R, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator R A hA_norm_R
  have hfixEq :
      Cfix =
        ((R ⊓ Subgroup.centralizer (A : Set X)).subgroupOf R) := by
    simpa [subgroupCentralizerIn] using
      fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn
        R A hA_norm_R
  have : Ccomm.Normal :=
    (commutatorAction_normal_and_invariant (A := A) (G := R)).1
  apply Set.Subset.antisymm
  · intro x hxR
    let xR : R := ⟨x, hxR⟩
    have hxTop : xR ∈ Ccomm ⊔ Cfix := by
      rw [sup_comm, hsup]
      exact Subgroup.mem_top xR
    rcases (Subgroup.mem_sup_of_normal_left.mp hxTop) with
      ⟨k, hk, c, hc, hkc⟩
    rw [Set.mem_mul]
    refine ⟨(k : X), ?_, (c : X), ?_, ?_⟩
    · rw [← hcommMap]
      exact ⟨k, hk, rfl⟩
    · rw [hfixEq] at hc
      exact hc
    · exact congrArg Subtype.val hkc
  · intro x hx
    rw [Set.mem_mul] at hx
    rcases hx with ⟨k, hk, c, hc, rfl⟩
    have hkR : k ∈ R := by
      rw [← hcommMap] at hk
      exact Subgroup.map_subtype_le Ccomm hk
    exact R.mul_mem hkR hc.1

theorem normal_two_le {Bx Tx N : Subgroup X} [N.Normal] (hNp : IsPGroup 2 N)
    (hBodd : Odd (Nat.card Bx)) (hT : IsPGroup 2 Tx) (hcard : Nat.card Bx * Nat.card Tx = Nat.card X) :
    N ≤ Tx := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (N ⊔ Tx : Subgroup X) := hNp.to_sup_of_normal_left hT
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have h1 : Nat.card (N ⊔ Tx : Subgroup X) ∣ Nat.card X :=
    Subgroup.card_subgroup_dvd_card _
  rw [hm, ← hcard] at h1
  have h2 : Nat.Coprime (2 ^ m) (Nat.card Bx) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hBodd)
  have h3 : 2 ^ m ∣ Nat.card Tx := Nat.Coprime.dvd_of_dvd_mul_left h2 h1
  have h4 : Nat.card (N ⊔ Tx : Subgroup X) ≤ Nat.card Tx := by
    rw [hm]; exact Nat.le_of_dvd Nat.card_pos h3
  have h5 := Subgroup.eq_of_le_of_card_ge (le_sup_right : Tx ≤ N ⊔ Tx) h4
  rw [h5]; exact le_sup_left

theorem part2 {Bx Tx : Subgroup X}
    (hBab : ∀ a ∈ Bx, ∀ b ∈ Bx, a * b = b * a) (hBodd : Odd (Nat.card Bx)) (hT : IsPGroup 2 Tx)
    (hperm : (Bx : Set X) * Tx = Tx * Bx) (hsup : Bx ⊔ Tx = ⊤)
    (A : Subgroup X) (hAB : A ≤ Bx)
    (hA : ∀ n ∈ Tx, n ∈ Subgroup.normalizer (Bx : Set X) → n ∈ Subgroup.normalizer (A : Set X)) :
    (Tx : Set X) = (⁅CFSG.pCore 2 X, A⁆ : Subgroup X) *
      ((Tx ⊓ Subgroup.normalizer (A : Set X) : Subgroup X) : Set X) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNn : (CFSG.pCore 2 X).Normal := CFSG.pCore_normal
  have hNp : IsPGroup 2 (CFSG.pCore 2 X) := CFSG.pCore_isPGroup
  have hF := fittingQuotient_eq_actor_image hBab hBodd hT hperm hsup
  have hcop0 : Nat.Coprime (Nat.card Bx) (Nat.card Tx) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]; exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hBodd)
  have hdisj : Bx ⊓ Tx = ⊥ := Subgroup.inf_eq_bot_of_coprime hcop0
  have hmul : (Bx : Set X) * (Tx : Set X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ Bx ⊔ Tx := by rw [hsup]; trivial
    obtain ⟨b, hb, t, ht, rfl⟩ := mem_sup_mul hperm hx
    exact Set.mem_mul.mpr ⟨b, hb, t, ht, rfl⟩
  have hcompl : Subgroup.IsComplement' Bx Tx :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj) hmul
  have hcard : Nat.card Bx * Nat.card Tx = Nat.card X := hcompl.card_mul_card
  have hNT : CFSG.pCore 2 X ≤ Tx := normal_two_le hNp hBodd hT hcard
  haveI hBbn : (Bx.map (QuotientGroup.mk' (CFSG.pCore 2 X))).Normal := by rw [hF]; infer_instance
  obtain ⟨S, hS⟩ : ∃ S : Subgroup X, S = (Bx.map (QuotientGroup.mk' (CFSG.pCore 2 X))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 X)) := ⟨_, rfl⟩
  haveI hSn : S.Normal := by rw [hS]; exact Subgroup.Normal.comap hBbn _
  have hmemS : ∀ s, s ∈ S ↔ ∃ h ∈ Bx, QuotientGroup.mk' (CFSG.pCore 2 X) h =
      QuotientGroup.mk' (CFSG.pCore 2 X) s := by
    intro s; rw [hS, Subgroup.mem_comap, Subgroup.mem_map]
  have hBS : Bx ≤ S := fun b hb => (hmemS b).mpr ⟨b, hb, rfl⟩
  have hNS : CFSG.pCore 2 X ≤ S := by
    intro n hn
    refine (hmemS n).mpr ⟨1, Bx.one_mem, ?_⟩
    simpa using ((QuotientGroup.eq_one_iff n).mpr hn).symm
  have cover : ∀ Hh : Subgroup X, (∀ s ∈ S, ∃ h ∈ Hh, QuotientGroup.mk' (CFSG.pCore 2 X) s =
      QuotientGroup.mk' (CFSG.pCore 2 X) h) → ∀ s ∈ S, ∃ n ∈ CFSG.pCore 2 X, ∃ h ∈ Hh, s = n * h := by
    intro Hh hHh s hs
    obtain ⟨h, hh, e⟩ := hHh s hs
    refine ⟨s * h⁻¹, ?_, h, hh, by group⟩
    rw [← QuotientGroup.eq_one_iff]
    show QuotientGroup.mk' (CFSG.pCore 2 X) (s * h⁻¹) = 1
    rw [map_mul, map_inv, e, mul_inv_cancel]
  have hmain : ∀ t ∈ Tx, ∃ n ∈ CFSG.pCore 2 X, n * t ∈ Subgroup.normalizer (Bx : Set X) := by
    intro t ht
    have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
    have hKS : Bx.map (MulAut.conj t).toMonoidHom ≤ S := by
      rintro _ ⟨b, hb, rfl⟩
      exact hSn.conj_mem b (hBS hb) t
    have hKodd : Odd (Nat.card (Bx.map (MulAut.conj t).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective hinj]; exact hBodd
    have hc1 : ∀ s ∈ S, ∃ h ∈ Bx, QuotientGroup.mk' (CFSG.pCore 2 X) s =
        QuotientGroup.mk' (CFSG.pCore 2 X) h := by
      intro s hs
      obtain ⟨h, hh, e⟩ := (hmemS s).mp hs
      exact ⟨h, hh, e.symm⟩
    have hc2 : ∀ s ∈ S, ∃ h ∈ Bx.map (MulAut.conj t).toMonoidHom,
        QuotientGroup.mk' (CFSG.pCore 2 X) s = QuotientGroup.mk' (CFSG.pCore 2 X) h := by
      intro s hs
      have hs' : t⁻¹ * s * t ∈ S := by simpa using hSn.conj_mem s hs t⁻¹
      obtain ⟨h0, hh0, e⟩ := (hmemS _).mp hs'
      refine ⟨t * h0 * t⁻¹, ⟨h0, hh0, rfl⟩, ?_⟩
      rw [map_mul, map_mul, e, map_mul, map_mul, map_inv]
      group
    obtain ⟨n, hn, hK⟩ := hall_conj (N := CFSG.pCore 2 X) (S := S) (Hh := Bx)
      (K := Bx.map (MulAut.conj t).toMonoidHom) hNp hNS hBS hKS hBodd hKodd (cover Bx hc1)
      (cover _ hc2)
    refine ⟨n, hn, ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have h1 : t * h * t⁻¹ ∈ Bx.map (MulAut.conj t).toMonoidHom := ⟨h, hh, rfl⟩
        rw [hK] at h1
        obtain ⟨b', hb', e⟩ := h1
        have e' : n⁻¹ * b' * n = t * h * t⁻¹ := by simpa using e
        have : n * t * h * (n * t)⁻¹ = b' := by
          calc n * t * h * (n * t)⁻¹ = n * (t * h * t⁻¹) * n⁻¹ := by group
            _ = n * (n⁻¹ * b' * n) * n⁻¹ := by rw [e']
            _ = b' := by group
        rw [this]; exact hb'
      · intro hh
        have h1 : n⁻¹ * (n * t * h * (n * t)⁻¹) * n ∈ Bx.map (MulAut.conj n⁻¹).toMonoidHom :=
          ⟨_, hh, by simp⟩
        rw [← hK] at h1
        obtain ⟨x', hx', e⟩ := h1
        have e' : t * x' * t⁻¹ = n⁻¹ * (n * t * h * (n * t)⁻¹) * n := by simpa using e
        have : x' = h := by
          have : t * x' * t⁻¹ = t * h * t⁻¹ := by rw [e']; group
          simpa using this
        rw [← this]; exact hx'
  have hAodd : Odd (Nat.card A) := Odd.of_dvd_nat hBodd (Subgroup.card_dvd_of_le hAB)
  have hAnorm : A ≤ Subgroup.normalizer ((CFSG.pCore 2 X : Subgroup X) : Set X) := by
    intro a _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hNn.conj_mem h hh a
    · intro hh
      have := hNn.conj_mem _ hh a⁻¹
      simpa [mul_assoc] using this
  have hdec := coprime_decomp hNp hAnorm hAodd
  have hcN : (⁅CFSG.pCore 2 X, A⁆ : Subgroup X) ≤ CFSG.pCore 2 X := Subgroup.commutator_le_left _ _
  apply Set.Subset.antisymm
  · intro t ht
    obtain ⟨n, hn, hnt⟩ := hmain t ht
    have hg : n * t ∈ Subgroup.normalizer (A : Set X) := hA _ (Tx.mul_mem (hNT hn) ht) hnt
    have hn' : n⁻¹ ∈ ((CFSG.pCore 2 X : Subgroup X) : Set X) := (CFSG.pCore 2 X).inv_mem hn
    rw [hdec] at hn'
    obtain ⟨c, hc, z, hz, hcz⟩ := hn'
    refine Set.mem_mul.mpr ⟨c, hc, z * (n * t), ⟨Tx.mul_mem (hNT hz.1) (Tx.mul_mem (hNT hn) ht), ?_⟩, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.centralizer_le_normalizer (A : Set X) hz.2) hg
    · calc c * (z * (n * t)) = (c * z) * (n * t) := by group
        _ = n⁻¹ * (n * t) := by rw [show c * z = n⁻¹ from hcz]
        _ = t := by group
  · rintro _ ⟨c, hc, g, hg, rfl⟩
    exact Tx.mul_mem (hNT (hcN hc)) hg.1

end OddActorSylowFactorization
namespace OddActorSylowFactorization

def conjAut {G : Type} [Group G] (B : Subgroup G) (g : G) (hg : ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B) :
    ↥B ≃* ↥B where
  toFun x := ⟨g * x * g⁻¹, (hg x).mp x.2⟩
  invFun x := ⟨g⁻¹ * x * g, by
    have := (hg (g⁻¹ * x * g)).mpr (by simpa [mul_assoc] using x.2)
    exact this⟩
  left_inv x := by ext; simp [mul_assoc]
  right_inv x := by ext; simp [mul_assoc]
  map_mul' x y := by ext; simp [mul_assoc]

theorem conj_mem_of_char {G : Type} [Group G] {B A : Subgroup G} (hAB : A ≤ B)
    (hchar : ∀ φ : ↥B ≃* ↥B, Subgroup.map φ.toMonoidHom (A.subgroupOf B) = A.subgroupOf B)
    (g : G) (hg : ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B) : g ∈ Subgroup.normalizer (A : Set G) := by
  have key : ∀ (g : G) (hg : ∀ x, x ∈ B ↔ g * x * g⁻¹ ∈ B), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
    intro g hg a ha
    have h1 : (⟨a, hAB ha⟩ : ↥B) ∈ A.subgroupOf B := ha
    have h2 : (conjAut B g hg).toMonoidHom ⟨a, hAB ha⟩ ∈ A.subgroupOf B := by
      rw [← hchar (conjAut B g hg)]; exact ⟨_, h1, rfl⟩
    exact h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have hg' : ∀ x, x ∈ B ↔ g⁻¹ * x * g⁻¹⁻¹ ∈ B := by
    intro x
    rw [hg (g⁻¹ * x * g⁻¹⁻¹)]
    simp [mul_assoc]
  have := key g⁻¹ hg' _ hx
  simpa [mul_assoc] using this

theorem norm_iff {G : Type} [Group G] {M A : Subgroup G} (hAM : A ≤ M) (t : M) :
    (t : G) ∈ Subgroup.normalizer (A : Set G) ↔
      t ∈ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    exact h x.1
  · intro h x
    have hM : x ∈ A ∨ (t : G) * x * (t : G)⁻¹ ∈ A → x ∈ M := by
      rintro (hx | hx)
      · exact hAM hx
      · have := M.mul_mem (M.mul_mem (M.inv_mem t.2) (hAM hx)) t.2
        simpa [mul_assoc] using this
    constructor
    · intro hx
      exact (h ⟨x, hM (Or.inl hx)⟩).mp hx
    · intro hx
      exact (h ⟨x, hM (Or.inr hx)⟩).mpr hx

end OddActorSylowFactorization
variable {G : Type} [Group G] [Finite G]

theorem actor_le_twoFitting_preimage_and_sylow_factorization {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h51 : OddPrimeClassTwoAction G p P T B e) (h53 : FaithfulBinaryIrreducibleAction G p P T B ρ) :
    B ≤ Section21.oTwoF (B ⊔ T) ∧
      ∀ A : Subgroup G, A ≤ B →
        (∀ φ : ↥B ≃* ↥B, Subgroup.map φ.toMonoidHom (A.subgroupOf B) = A.subgroupOf B) →
        (T : Set G) =
          ((⁅CFSG.Open.pCoreOf 2 (B ⊔ T), A⁆ : Subgroup G) : Set G) *
            ((T ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := by
  have hset := h51.setting
  have hBM : B ≤ B ⊔ T := le_sup_left
  have hTM : T ≤ B ⊔ T := le_sup_right
  set M : Subgroup G := B ⊔ T with hM
  have hBab : ∀ a ∈ B.subgroupOf M, ∀ b ∈ B.subgroupOf M, a * b = b * a := by
    intro a ha b hb
    have := congrArg Subtype.val (hset.abelian.is_comm.comm ⟨a.1, ha⟩ ⟨b.1, hb⟩)
    exact Subtype.ext (by simpa using this)
  have hBodd : Odd (Nat.card (B.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv]; exact hset.oddOrder
  have hT : IsPGroup 2 (T.subgroupOf M) :=
    hset.twoGroup.comap_of_injective M.subtype Subtype.coe_injective
  have hperm : ((B.subgroupOf M : Subgroup M) : Set M) * (T.subgroupOf M : Subgroup M) =
      (T.subgroupOf M : Subgroup M) * (B.subgroupOf M : Subgroup M) := by
    have hp := hset.prod_comm
    ext x
    constructor
    · rintro ⟨b, hb, t, ht, rfl⟩
      have : (b : G) * t ∈ (T : Set G) * B := by
        rw [hp]; exact ⟨b, hb, t, ht, rfl⟩
      obtain ⟨t', ht', b', hb', e⟩ := this
      exact ⟨⟨t', hTM ht'⟩, ht', ⟨b', hBM hb'⟩, hb', Subtype.ext e⟩
    · rintro ⟨t, ht, b, hb, rfl⟩
      have : (t : G) * b ∈ (B : Set G) * T := by
        rw [← hp]; exact ⟨t, ht, b, hb, rfl⟩
      obtain ⟨b', hb', t', ht', e⟩ := this
      exact ⟨⟨b', hBM hb'⟩, hb', ⟨t', hTM ht'⟩, ht', Subtype.ext e⟩
  have hsup : B.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hBM hTM, ← hM, Subgroup.subgroupOf_self]
  have hF := OddActorSylowFactorization.fittingQuotient_eq_actor_image hBab hBodd hT hperm hsup
  refine ⟨?_, ?_⟩
  · intro b hb
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥M) (⟨b, hBM hb⟩ : M) ∈
        CFSG.fittingSubgroup (↥M ⧸ CFSG.pCore 2 ↥M) := by
      rw [← hF]; exact ⟨⟨b, hBM hb⟩, hb, rfl⟩
    rw [oTwoF_eq]
    exact Subgroup.mem_map.mpr ⟨⟨b, hBM hb⟩, h1, rfl⟩
  · intro A hAB hchar
    have hAM : A ≤ M := hAB.trans hBM
    have hA' : A.subgroupOf M ≤ B.subgroupOf M := fun x hx => hAB hx
    have hnormB : ∀ n : M, n ∈ T.subgroupOf M →
        n ∈ Subgroup.normalizer ((B.subgroupOf M : Subgroup M) : Set M) →
        n ∈ Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) := by
      intro n _ hnB
      rw [Subgroup.mem_normalizer_iff] at hnB
      have hg : ∀ x : G, x ∈ B ↔ (n : G) * x * (n : G)⁻¹ ∈ B := by
        intro x
        have hxM : x ∈ B ∨ (n : G) * x * (n : G)⁻¹ ∈ B → x ∈ M := by
          rintro (hx | hx)
          · exact hBM hx
          · have := M.mul_mem (M.mul_mem (M.inv_mem n.2) (hBM hx)) n.2
            simpa [mul_assoc] using this
        constructor
        · intro hx
          exact (hnB ⟨x, hBM hx⟩).mp hx
        · intro hx
          exact (hnB ⟨x, hxM (Or.inr hx)⟩).mpr hx
      exact (OddActorSylowFactorization.norm_iff hAM n).mp (OddActorSylowFactorization.conj_mem_of_char hAB hchar _ hg)
    have h2 := OddActorSylowFactorization.part2 hBab hBodd hT hperm hsup (A.subgroupOf M) hA' hnormB
    have e1 : M.subtype '' ((T.subgroupOf M : Subgroup M) : Set M) = (T : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hx; exact ⟨⟨x, hTM hx⟩, hx, rfl⟩
    have e2 : M.subtype '' ((⁅CFSG.pCore 2 ↥M, A.subgroupOf M⁆ : Subgroup M) : Set M) =
        ((⁅CFSG.Open.pCoreOf 2 M, A⁆ : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_map, Subgroup.map_commutator]
      have h3 : Subgroup.map M.subtype (A.subgroupOf M) = A := by
        rw [Subgroup.subgroupOf_map_subtype]; exact inf_eq_left.mpr hAM
      have h4 : CFSG.Open.pCoreOf 2 M = Subgroup.map M.subtype (CFSG.pCore 2 ↥M) := by
        unfold CFSG.Open.pCoreOf
        rw [OddActorSylowFactorization.openPCore_eq]
      rw [h3, h4]
    have e3 : M.subtype '' (((T.subgroupOf M : Subgroup M) ⊓
        Subgroup.normalizer ((A.subgroupOf M : Subgroup M) : Set M) : Subgroup M) : Set M) =
        ((T ⊓ Subgroup.normalizer (A : Set G) : Subgroup G) : Set G) := by
      ext x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
        exact ⟨hy1, (OddActorSylowFactorization.norm_iff hAM y).mpr hy2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨⟨x, hTM hx1⟩, ⟨hx1, (OddActorSylowFactorization.norm_iff hAM ⟨x, hTM hx1⟩).mp hx2⟩, rfl⟩
    calc (T : Set G) = M.subtype '' ((T.subgroupOf M : Subgroup M) : Set M) := e1.symm
      _ = _ := by rw [h2, Set.image_mul, e2, e3]

end Section5
end CFSG.LocalAnalysis.RankThreeUC
