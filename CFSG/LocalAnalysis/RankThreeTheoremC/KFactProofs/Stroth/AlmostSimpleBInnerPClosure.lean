module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open CFSG CFSG.Open Subgroup
open scoped commutatorElement

section Closure

@[expose] def pElemClosure (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.closure {x : G | ∃ k : ℕ, x ^ p ^ k = 1}

@[expose] def OddPCoreInClosure (p : ℕ) (G : Type*) [Group G] : Prop :=
  ∀ K : Subgroup G, K.Normal → K ≤ pElemClosure p G → Nat.Coprime p (Nat.card K) →
    Odd (Nat.card K)

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

theorem mem_pElemClosure_of_pElem {x : G} (hx : ∃ k : ℕ, x ^ p ^ k = 1) :
    x ∈ pElemClosure p G :=
  Subgroup.subset_closure hx

theorem map_pElemClosure_le (f : G →* H) :
    (pElemClosure p G).map f ≤ pElemClosure p H := by
  rw [pElemClosure, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, ⟨k, hk⟩, rfl⟩
  exact mem_pElemClosure_of_pElem ⟨k, by rw [← map_pow, hk, map_one]⟩

instance pElemClosure_normal : (pElemClosure p G).Normal := by
  refine ⟨fun n hn g => ?_⟩
  exact map_pElemClosure_le (p := p) (MulAut.conj g).toMonoidHom ⟨n, hn, rfl⟩

theorem exists_pElem_lift [Finite G] (hp : p.Prime) (f : G →* H) {a : G} {b : H}
    (hab : f a = b) (hb : ∃ k : ℕ, b ^ p ^ k = 1) :
    ∃ a' : G, (∃ k : ℕ, a' ^ p ^ k = 1) ∧ f a' = b := by
  have hn : orderOf a ≠ 0 := (orderOf_pos a).ne'
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hco : Nat.Coprime (p ^ e) m := Nat.Coprime.pow_left e (hp.coprime_iff_not_dvd.2 hpm)
  obtain ⟨s, hs1, hs0⟩ := Nat.chineseRemainder hco 1 0
  have hms : m ∣ s := (Nat.modEq_zero_iff_dvd).1 hs0
  refine ⟨a ^ s, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hnm, mul_comm s]
    exact Nat.mul_dvd_mul_left _ hms
  · rw [map_pow, hab]
    obtain ⟨j, hj⟩ := hb
    have hord : orderOf b ∣ p ^ e := by
      have h1 : orderOf b ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 h1
      have h2 : orderOf b ∣ orderOf a := hab ▸ orderOf_map_dvd f a
      rw [hnm, hi] at h2
      rw [hi]
      exact (Nat.Coprime.pow_left i (hp.coprime_iff_not_dvd.2 hpm)).dvd_of_dvd_mul_right h2
    calc b ^ s = b ^ 1 := (pow_eq_pow_iff_modEq).2 (Nat.ModEq.of_dvd hord hs1)
      _ = b := pow_one b

theorem map_pElemClosure_eq [Finite G] (hp : p.Prime) (f : G →* H)
    (hf : Function.Surjective f) : (pElemClosure p G).map f = pElemClosure p H := by
  refine le_antisymm (map_pElemClosure_le f) ?_
  rw [pElemClosure, Subgroup.closure_le]
  intro b hb
  obtain ⟨a, rfl⟩ := hf b
  obtain ⟨a', ha', hfa'⟩ := exists_pElem_lift hp f rfl hb
  exact ⟨a', mem_pElemClosure_of_pElem ha', hfa'⟩

theorem pElemClosure_eq_bot_of_not_dvd [Finite G] (hp : p.Prime) (h : ¬ p ∣ Nat.card G) :
    pElemClosure p G = ⊥ := by
  rw [pElemClosure, eq_bot_iff, Subgroup.closure_le]
  rintro x ⟨k, hk⟩
  rw [SetLike.mem_coe, Subgroup.mem_bot]
  have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ Nat.card G := orderOf_dvd_natCard x
  have hcop : Nat.Coprime (p ^ k) (Nat.card G) :=
    Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.2 h)
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))

end Closure

section OddCard

theorem odd_natCard_of_forall_sq {K : Type*} [Group K] [Finite K]
    (h : ∀ x : K, x ^ 2 = 1 → x = 1) : Odd (Nat.card K) := by
  by_contra hne
  have h2 : 2 ∣ Nat.card K := (Nat.not_odd_iff_even.1 hne).two_dvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 h2
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have := h x hx2
  rw [this, orderOf_one] at hx
  omega

theorem eq_one_of_sq_eq_one_of_odd_natCard {K : Type*} [Group K] [Finite K]
    (hodd : Odd (Nat.card K)) {x : K} (hx : x ^ 2 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card K := orderOf_dvd_natCard x
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact orderOf_eq_one_iff.1 h
  · exfalso
    rw [h] at h2
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)

end OddCard

section Stability

variable {p : ℕ} {G H : Type*} [Group G] [Group H]

theorem OddPCoreInClosure.of_not_dvd [Finite G] (hp : p.Prime) (h : ¬ p ∣ Nat.card G) :
    OddPCoreInClosure p G := by
  intro K _ hKle _
  have hK : K = ⊥ := le_bot_iff.1 ((pElemClosure_eq_bot_of_not_dvd hp h) ▸ hKle)
  subst hK
  simp

theorem OddPCoreInClosure.of_odd_core [Finite G]
    (h : ∀ K : Subgroup G, K.Normal → Nat.Coprime p (Nat.card K) → Odd (Nat.card K)) :
    OddPCoreInClosure p G := fun K hK _ hcop => h K hK hcop

theorem OddPCoreInClosure.of_mulEquiv (e : G ≃* H) (h : OddPCoreInClosure p G) :
    OddPCoreInClosure p H := by
  intro K hK hKle hcop
  have hK' : (K.map e.symm.toMonoidHom).Normal := hK.map _ e.symm.surjective
  have hle : K.map e.symm.toMonoidHom ≤ pElemClosure p G :=
    (Subgroup.map_mono hKle).trans (map_pElemClosure_le e.symm.toMonoidHom)
  have hcard : Nat.card (K.map e.symm.toMonoidHom) = Nat.card K :=
    Subgroup.card_map_of_injective e.symm.injective
  have := h _ hK' hle (hcard ▸ hcop)
  rwa [hcard] at this

theorem OddPCoreInClosure.of_normal [Finite G] (hp : p.Prime) (N : Subgroup G) [N.Normal]
    (h : OddPCoreInClosure p G) : OddPCoreInClosure p N := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro K hK hKle hcop
  set KG : Subgroup G := K.map N.subtype with hKG
  set PN : Subgroup G := (pPrimeCore p ↥N).map N.subtype with hPN
  have hPNnormal : PN.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hx
    have h1 : (pPrimeCore p ↥N).map (MulAut.conjNormal (H := N) g).toMonoidHom =
        pPrimeCore p ↥N := by
      have := (Subgroup.characteristic_iff_map_eq (H := pPrimeCore p ↥N)).1 inferInstance
        (MulAut.conjNormal (H := N) g)
      simpa using this
    have h2 : (MulAut.conjNormal (H := N) g) y ∈ pPrimeCore p ↥N := by
      rw [← h1]
      exact ⟨y, hy, rfl⟩
    refine ⟨_, h2, ?_⟩
    simp [MulAut.conjNormal_apply]
  have hKPN : KG ≤ PN := Subgroup.map_mono (le_sSup ⟨hK, hcop⟩)
  have hKGle : KG ≤ pElemClosure p G :=
    (Subgroup.map_mono hKle).trans (map_pElemClosure_le N.subtype)
  have hcl_le : Subgroup.normalClosure (KG : Set G) ≤ pElemClosure p G :=
    Subgroup.normalClosure_le_normal hKGle
  have hcl_PN : Subgroup.normalClosure (KG : Set G) ≤ PN :=
    Subgroup.normalClosure_le_normal hKPN
  have hcopPN : Nat.Coprime p (Nat.card PN) := by
    rw [hPN, Subgroup.card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  have hcopcl : Nat.Coprime p (Nat.card (Subgroup.normalClosure (KG : Set G))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hcl_PN) hcopPN
  have hodd := h _ inferInstance hcl_le hcopcl
  have hKcard : Nat.card KG = Nat.card K := Subgroup.card_map_of_injective N.subtype_injective
  rw [← hKcard]
  exact hodd.of_dvd_nat (Subgroup.card_dvd_of_le (Subgroup.le_normalClosure))

theorem exists_normal_pPrime_map_eq_range {T : Type*} [Group T] [Finite T] (hp : p.Prime)
    (φ : T →* H) (hker : φ.ker ≤ Subgroup.center T) (hcop : Nat.Coprime p (Nat.card φ.range)) :
    ∃ T' : Subgroup T, T'.Normal ∧ Nat.Coprime p (Nat.card T') ∧ T'.map φ = φ.range ∧
      ∀ t : T, t ∈ T' ↔ Nat.Coprime p (orderOf t) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P⟩ : Nonempty (Sylow p T) := inferInstance
  have hPker : (P : Subgroup T) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
    have hk' : x ^ p ^ k = 1 := congrArg Subtype.val hk
    have h1 : orderOf (φ x) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk', map_one])
    have h2 : orderOf (φ x) ∣ Nat.card φ.range :=
      Subgroup.orderOf_dvd_natCard φ.range (MonoidHom.mem_range.2 ⟨x, rfl⟩)
    have hc : Nat.Coprime (p ^ k) (Nat.card φ.range) := Nat.Coprime.pow_left k hcop
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hc.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))
  have hPc : (P : Subgroup T) ≤ Subgroup.center T := hPker.trans hker
  have hN : normalizer (P : Subgroup T) ≤ centralizer (P : Set T) := by
    intro g _
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact ((Subgroup.mem_center_iff.1 (hPc hh)) g).symm
  have hcomp := MonoidHom.ker_transferSylow_isComplement' P hN
  have hnd := MonoidHom.not_dvd_card_ker_transferSylow P hN
  set T' := (MonoidHom.transferSylow P hN).ker with hT'
  have hdisj : T' ⊓ (P : Subgroup T) = ⊥ := disjoint_iff.1 hcomp.disjoint
  have hsup : T' ⊔ (P : Subgroup T) = ⊤ := hcomp.sup_eq_top
  refine ⟨T', inferInstance, hp.coprime_iff_not_dvd.2 hnd, ?_, ?_⟩
  · have : T'.map φ = (T' ⊔ (P : Subgroup T)).map φ := by
      rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 hPker, sup_bot_eq]
    rw [this, hsup, ← MonoidHom.range_eq_map]
  · intro t
    constructor
    · intro ht
      exact Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard T' ht)
        (hp.coprime_iff_not_dvd.2 hnd)
    · intro hcopt
      have ht : t ∈ (↑(T' ⊔ (P : Subgroup T)) : Set T) := by rw [hsup]; trivial
      rw [Subgroup.normal_mul] at ht
      obtain ⟨a, ha, b, hb, hab⟩ := ht
      have hab' : a * b = t := hab
      subst hab'
      have hbc : Commute a b := ((Subgroup.mem_center_iff.1 (hPc hb)) a)
      have hm : (a * b) ^ orderOf (a * b) = 1 := pow_orderOf_eq_one _
      rw [hbc.mul_pow] at hm
      have hbm : b ^ orderOf (a * b) ∈ T' ⊓ (P : Subgroup T) := by
        refine ⟨?_, P.pow_mem hb _⟩
        have : b ^ orderOf (a * b) = (a ^ orderOf (a * b))⁻¹ := eq_inv_of_mul_eq_one_right hm
        rw [this]
        exact T'.inv_mem (T'.pow_mem ha _)
      rw [hdisj, Subgroup.mem_bot] at hbm
      obtain ⟨k, hk⟩ := P.isPGroup' ⟨b, hb⟩
      have hk' : b ^ p ^ k = 1 := congrArg Subtype.val hk
      have h1 : orderOf b ∣ orderOf (a * b) := orderOf_dvd_of_pow_eq_one hbm
      have h2 : orderOf b ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hc : Nat.Coprime (p ^ k) (orderOf (a * b)) := Nat.Coprime.pow_left k hcopt
      have hb1 : b = 1 :=
        orderOf_eq_one_iff.1 (Nat.dvd_one.1 (hc.gcd_eq_one ▸ Nat.dvd_gcd h2 h1))
      rw [hb1, mul_one]
      exact ha

theorem OddPCoreInClosure.of_surjective_ker_le_center [Finite G] (hp : p.Prime) (f : G →* H)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center G)
    (h : OddPCoreInClosure p G) : OddPCoreInClosure p H := by
  intro K hK hKle hcop
  set T : Subgroup G := K.comap f ⊓ pElemClosure p G with hT
  let φ : ↥T →* H := f.comp T.subtype
  have hrange : φ.range = K := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      exact t.2.1
    · intro hy
      have hy' : y ∈ (pElemClosure p G).map f := by
        rw [map_pElemClosure_eq hp f hf]
        exact hKle hy
      obtain ⟨g, hg, rfl⟩ := hy'
      exact ⟨⟨g, ⟨hy, hg⟩⟩, rfl⟩
  have hker' : φ.ker ≤ Subgroup.center ↥T := by
    intro t ht
    rw [Subgroup.mem_center_iff]
    intro t'
    apply Subtype.ext
    have hc : (t : G) ∈ Subgroup.center G := hker (by simpa [φ] using ht)
    exact (Subgroup.mem_center_iff.1 hc (t' : G))
  obtain ⟨T', hT'n, hT'cop, hT'map, hT'char⟩ :=
    exists_normal_pPrime_map_eq_range hp φ hker' (by rw [hrange]; exact hcop)
  have hT''n : (T'.map T.subtype).Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨t, ht, rfl⟩ := hx
    have ht' : t ∈ T' := ht
    have hconj : (MulAut.conjNormal (H := T) g) t ∈ T' := by
      rw [hT'char]
      have : orderOf ((MulAut.conjNormal (H := T) g) t) = orderOf t :=
        MulEquiv.orderOf_eq _ _
      rw [this]
      exact (hT'char t).1 ht'
    exact ⟨_, hconj, by simp [MulAut.conjNormal_apply]⟩
  have hle : T'.map T.subtype ≤ pElemClosure p G := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2.2
  have hcop'' : Nat.Coprime p (Nat.card (T'.map T.subtype)) := by
    rw [Subgroup.card_map_of_injective T.subtype_injective]
    exact hT'cop
  have hodd := h _ hT''n hle hcop''
  have hmapK : (T'.map T.subtype).map f = K := by
    rw [Subgroup.map_map]
    have : f.comp T.subtype = φ := rfl
    rw [this, hT'map, hrange]
  have hdvd : Nat.card K ∣ Nat.card (T'.map T.subtype) := by
    have := Subgroup.card_map_dvd (H := T'.map T.subtype) f
    rwa [hmapK] at this
  exact hodd.of_dvd_nat hdvd

theorem OddPCoreInClosure.pi {ι : Type*} [Finite ι] {G : ι → Type*} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] (hp : p.Prime) (h : ∀ i, OddPCoreInClosure p (G i)) :
    OddPCoreInClosure p (∀ i, G i) := by
  classical
  intro K hK hKle hcop
  haveI : Finite (∀ i, G i) := inferInstance
  have hKi : ∀ i, Odd (Nat.card (K.map (Pi.evalMonoidHom G i))) := by
    intro i
    have hsurj : Function.Surjective (Pi.evalMonoidHom G i) := fun y =>
      ⟨Pi.mulSingle i y, by simp⟩
    refine h i _ (hK.map _ hsurj) ?_ ?_
    · exact (Subgroup.map_mono hKle).trans (map_pElemClosure_le _)
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ _) hcop
  refine odd_natCard_of_forall_sq fun x hx2 => ?_
  have hx2' : (x : ∀ i, G i) ^ 2 = 1 := by
    simpa using congrArg Subtype.val hx2
  refine Subtype.ext (funext fun i => ?_)
  have hxi : ((x : ∀ i, G i) i) ∈ K.map (Pi.evalMonoidHom G i) := ⟨x, x.2, rfl⟩
  have hsq : (⟨(x : ∀ i, G i) i, hxi⟩ : K.map (Pi.evalMonoidHom G i)) ^ 2 = 1 := by
    refine Subtype.ext ?_
    have := congrFun hx2' i
    simpa using this
  haveI := Finite.of_injective (fun y : K.map (Pi.evalMonoidHom G i) => (y : G i))
    Subtype.val_injective
  have := eq_one_of_sq_eq_one_of_odd_natCard (hKi i) hsq
  exact congrArg Subtype.val this

end Stability

section Application

variable {p : ℕ} {X : Type*} [Group X]

theorem relPPrimeCore_eq_map [Finite X] (hp : p.Prime) (C : Subgroup X) :
    relPPrimeCore p C = (pPrimeCore p ↥C).map C.subtype := by
  haveI : Fact p.Prime := ⟨hp⟩
  apply le_antisymm
  · refine sSup_le fun N hN => ?_
    obtain ⟨hNC, hNn, hNc⟩ := hN
    have h1 : N.subgroupOf C ≤ pPrimeCore p ↥C := by
      refine le_sSup ⟨hNn, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNC).toEquiv]
      exact hNc
    calc N = (N.subgroupOf C).map C.subtype := (Subgroup.map_subgroupOf_eq_of_le hNC).symm
      _ ≤ _ := Subgroup.map_mono h1
  · refine le_sSup ⟨?_, ?_, ?_⟩
    · rintro _ ⟨y, -, rfl⟩
      exact y.2
    · show (Subgroup.comap C.subtype ((pPrimeCore p ↥C).map C.subtype)).Normal
      rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
      infer_instance
    · rw [Subgroup.card_map_of_injective C.subtype_injective]
      exact pPrimeCore_coprime_card

theorem relPPrimeCore_le (C : Subgroup X) : relPPrimeCore p C ≤ C :=
  sSup_le fun _ hN => hN.1

theorem relPPrimeCore_normal [Finite X] (hp : p.Prime) (C : Subgroup X) :
    ((relPPrimeCore p C).subgroupOf C).Normal := by
  rw [relPPrimeCore_eq_map hp]
  show (Subgroup.comap C.subtype ((pPrimeCore p ↥C).map C.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective C.subtype_injective]
  infer_instance

theorem coprime_card_relPPrimeCore [Finite X] (hp : p.Prime) (C : Subgroup X) :
    Nat.Coprime p (Nat.card (relPPrimeCore p C)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [relPPrimeCore_eq_map hp, Subgroup.card_map_of_injective C.subtype_injective]
  exact pPrimeCore_coprime_card

theorem commutator_eq_bot_of_oddPCore [Finite X] (hp : p.Prime) {C D S : Subgroup X}
    (hC : OddPCoreInClosure p ↥C) (hDC : D ≤ C) (hDp : ∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k = 1)
    (hSR : S ≤ relPPrimeCore p C) (hS2 : IsPGroup 2 S)
    (hDS : D ≤ Subgroup.normalizer (S : Set X)) : ⁅S, D⁆ = ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  set K : Subgroup ↥C := pPrimeCore p ↥C ⊓ pElemClosure p ↥C with hK
  have hKcop : Nat.Coprime p (Nat.card K) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) pPrimeCore_coprime_card
  have hodd := hC K inferInstance inf_le_right hKcop
  have hcomm : ⁅S, D⁆ ≤ K.map C.subtype := by
    rw [Subgroup.commutator_le]
    intro s hs d hd
    have hsR : s ∈ (pPrimeCore p ↥C).map C.subtype := by
      rw [← relPPrimeCore_eq_map hp]
      exact hSR hs
    obtain ⟨s', hs', rfl⟩ := hsR
    have hdC : d ∈ C := hDC hd
    have hd' : (⟨d, hdC⟩ : ↥C) ∈ pElemClosure p ↥C := by
      obtain ⟨k, hk⟩ := hDp d hd
      exact mem_pElemClosure_of_pElem ⟨k, Subtype.ext hk⟩
    refine ⟨⁅s', ⟨d, hdC⟩⁆, ⟨?_, ?_⟩, rfl⟩
    · have h1 := (pPrimeCore_normal (p := p) (G := ↥C)).conj_mem s'⁻¹ (inv_mem hs') ⟨d, hdC⟩
      have h2 : ⁅s', (⟨d, hdC⟩ : ↥C)⁆ = s' * (⟨d, hdC⟩ * s'⁻¹ * ⟨d, hdC⟩⁻¹) := by
        simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact mul_mem hs' h1
    · have h1 := (pElemClosure_normal (p := p) (G := ↥C)).conj_mem ⟨d, hdC⟩ hd' s'
      have h2 : ⁅s', (⟨d, hdC⟩ : ↥C)⁆ = (s' * ⟨d, hdC⟩ * s'⁻¹) * ⟨d, hdC⟩⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [h2]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hd')
  have hleS : ⁅S, D⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro s hs d hd
    have h1 : d * s⁻¹ * d⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 (hDS hd) s⁻¹).1 (inv_mem hs)
    have h2 : ⁅s, d⁆ = s * (d * s⁻¹ * d⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact mul_mem hs h1
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨k, hkK, hkx⟩ := hcomm hx
  obtain ⟨j, hj⟩ := hS2 ⟨x, hleS hx⟩
  have hj' : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h1 : orderOf x ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hj'
  have h2 : orderOf k ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hkK
  have h3 : orderOf x = orderOf k := by
    rw [← hkx]
    exact Subgroup.orderOf_coe k
  rw [h3] at h1
  have h4 : orderOf k ∣ 1 := by
    have hc : Nat.Coprime (2 ^ j) (Nat.card K) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd)
    exact hc.gcd_eq_one ▸ Nat.dvd_gcd h1 h2
  rw [← orderOf_eq_one_iff, h3]
  exact Nat.dvd_one.1 h4

end Application

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
