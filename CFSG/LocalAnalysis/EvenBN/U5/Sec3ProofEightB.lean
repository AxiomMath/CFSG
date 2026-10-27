module

public import CFSG.LocalAnalysis.EvenBN.U5.CaseBSharedParts
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3EThree
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B6Two
public import CFSG.LocalAnalysis.EvenBN.U5.ModelParabolic
public import CFSG.LocalAnalysis.EvenBN.U5.ModelParabolicTwo
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.EvenBN.GMSK.QuasiCentre

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Blueprint
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.EvenBN.Common.NormalizerQuotient
open scoped MatrixGroups commutatorElement

section Generic

theorem sec38b_eq_of_mem_zpowers {H : Type*} [Group H] {t z : H} (ht : orderOf t = 2)
    (hz : z ∈ zpowers t) (hz1 : z ≠ 1) : z = t := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hz
  have e := zpow_mod_orderOf t k
  rw [ht] at e
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    apply hz1
    rw [← e]
    have : k % ((2 : ℕ) : ℤ) = 0 := by exact_mod_cast h0
    rw [this, zpow_zero]
  · rw [← e]
    have : k % ((2 : ℕ) : ℤ) = 1 := by exact_mod_cast h1
    rw [this, zpow_one]

theorem sec38b_card_le_two {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H}
    (ht : orderOf t = 2) (htA : t ∈ centralizer (A : Set H))
    (hQ : ∀ Q : Subgroup H, Q ≤ centralizer (A : Set H) ⊓ centralizer ({t} : Set H) →
      IsPGroup 2 Q → Q ≤ zpowers t) :
    ∀ P : Subgroup H, P ≤ centralizer (A : Set H) → IsPGroup 2 P → Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (A : Set H) with hC
  have htC : zpowers t ≤ C := zpowers_le.2 htA
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨S, hS⟩ := (hz2.of_equiv (subgroupOfEquivOfLe htC).symm).exists_le_sylow
  set Q : Subgroup H := (S : Subgroup C).map C.subtype with hQdef
  have hQC : Q ≤ C := map_subtype_le _
  have hQ2 : IsPGroup 2 Q := S.isPGroup'.map _
  have htQ : zpowers t ≤ Q := fun x hx => ⟨⟨x, htC hx⟩, hS hx, rfl⟩
  have hQeq : Q = zpowers t := by
    refine le_antisymm ?_ htQ
    have htQ' : t ∈ Q := htQ (mem_zpowers t)
    haveI : Nontrivial ↥Q := by
      refine ⟨⟨⟨t, htQ'⟩, 1, fun h1 => ?_⟩⟩
      have : t = 1 := congrArg Subtype.val h1
      rw [this, orderOf_one] at ht
      omega
    haveI : Nontrivial (center ↥Q) := hQ2.center_nontrivial
    have hZ2 : IsPGroup 2 (center ↥Q) := hQ2.to_subgroup _
    obtain ⟨n, hn, hcard⟩ := (hZ2.nontrivial_iff_card).1 inferInstance
    have hdvd : 2 ∣ Nat.card (center ↥Q) := by
      rw [hcard]; exact dvd_pow_self 2 hn.ne'
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥Q) 2 hdvd
    set z' : H := (((z : center ↥Q) : ↥Q) : H) with hz'def
    have hz'o : orderOf z' = 2 := by
      rw [hz'def, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
    have hz'1 : z' ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz'o; omega
    have hz'Q : z' ∈ Q := ((z : center ↥Q) : ↥Q).2
    have hzc : ∀ y : ↥Q, y * ((z : center ↥Q) : ↥Q) = ((z : center ↥Q) : ↥Q) * y :=
      fun y => Subgroup.mem_center_iff.1 z.2 y
    have htz : t * z' = z' * t := congrArg Subtype.val (hzc ⟨t, htQ'⟩)
    have hz't : z' ∈ centralizer ({t} : Set H) := mem_centralizer_singleton_iff.2 htz.symm
    have hsup : zpowers z' ⊔ zpowers t ≤ centralizer (A : Set H) ⊓ centralizer ({t} : Set H) := by
      refine sup_le (zpowers_le.2 ⟨hQC hz'Q, hz't⟩) (zpowers_le.2 ⟨htA, ?_⟩)
      exact mem_centralizer_singleton_iff.2 rfl
    have hzQ : zpowers z' ⊔ zpowers t ≤ Q := sup_le (zpowers_le.2 hz'Q) (zpowers_le.2 htQ')
    have hmem := hQ _ hsup (hQ2.to_le hzQ)
    have hz'mem : z' ∈ zpowers t := hmem (mem_sup_left (mem_zpowers z'))
    have hz'eq : z' = t := sec38b_eq_of_mem_zpowers ht hz'mem hz'1
    have hQt : Q ≤ centralizer ({t} : Set H) := fun x hx => by
      refine mem_centralizer_singleton_iff.2 ?_
      have h2 : x * z' = z' * x := congrArg Subtype.val (hzc ⟨x, hx⟩)
      rw [hz'eq] at h2
      exact h2
    exact hQ Q (le_inf hQC hQt) hQ2
  have hcardS : Nat.card (S : Subgroup C) = 2 := by
    rw [← card_map_of_injective C.subtype_injective]
    change Nat.card Q = 2
    rw [hQeq, Nat.card_zpowers, ht]
  intro P hPC hP
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP.of_equiv (subgroupOfEquivOfLe hPC).symm
  obtain ⟨S', hS'⟩ := hP'.exists_le_sylow
  calc Nat.card P = Nat.card (P.subgroupOf C) :=
        Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv.symm
    _ ≤ Nat.card S' := card_le_of_le hS'
    _ = Nat.card S := Nat.card_congr (Sylow.equiv S' S).toEquiv
    _ = 2 := hcardS

theorem sec38b_normal_two_group_eq_bot {X : Type*} [Group X] [Finite X]
    (hX : CFSG.Open.IsQuasisimple X)
    (hZ : ∀ z ∈ center X, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1)
    (Y : Subgroup X) [hYn : Y.Normal] (hY : IsPGroup 2 Y) : Y = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (X ⧸ center X) := hX.2
  have hmapN : (Y.map (QuotientGroup.mk' (center X))).Normal :=
    hYn.map _ (QuotientGroup.mk'_surjective _)
  haveI := hmapN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Y.map (QuotientGroup.mk' (center X))) with hb | ht
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hb
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨k, hk⟩ := hY ⟨y, hy⟩
    have hyk : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact Subgroup.mem_bot.2 (hZ y (hb hy) k hyk)
  · exfalso
    have hdec : ∀ x : X, ∃ z ∈ center X, QuotientGroup.mk' Y x = QuotientGroup.mk' Y z := by
      intro x
      have : QuotientGroup.mk' (center X) x ∈ Y.map (QuotientGroup.mk' (center X)) := by
        rw [ht]; exact mem_top _
      obtain ⟨y, hy, hyx⟩ := this
      have hz : y⁻¹ * x ∈ center X := by
        rw [← QuotientGroup.ker_mk' (center X), MonoidHom.mem_ker, map_mul, map_inv, hyx,
          inv_mul_cancel]
      refine ⟨y⁻¹ * x, hz, ?_⟩
      have hy1 : QuotientGroup.mk' Y y = 1 := (QuotientGroup.eq_one_iff y).2 hy
      rw [map_mul, map_inv, hy1, inv_one, one_mul]
    have hcomm : commutator X ≤ Y := by
      rw [_root_.commutator_def]
      refine Subgroup.commutator_le.2 fun g1 _ g2 _ => ?_
      obtain ⟨z1, hz1, e1⟩ := hdec g1
      obtain ⟨z2, hz2, e2⟩ := hdec g2
      have hz12 : ⁅z1, z2⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_center_iff.1 hz2 z1)
      have h1 : QuotientGroup.mk' Y ⁅g1, g2⁆ = 1 := by
        rw [map_commutatorElement, e1, e2, ← map_commutatorElement, hz12, map_one]
      exact (QuotientGroup.eq_one_iff _).1 h1
    have hYtop : Y = ⊤ := top_le_iff.1 (hX.1 ▸ hcomm)
    haveI : IsPGroup 2 X := by
      subst hYtop
      exact hY.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent X := IsPGroup.isNilpotent this
    haveI : Group.IsPerfect X := ⟨hX.1⟩
    haveI : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
    exact Group.IsPerfect.not_isNilpotent X inferInstance

theorem sec38b_mem_map_conj {G : Type*} [Group G] (g : G) (Y : Subgroup G) (x : G) :
    x ∈ Y.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ Y := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem sec38b_conj_stable {G : Type*} [Group G] {V X : Subgroup G} {g : G}
    (hgV : g ∈ normalizer (V : Set G)) (hgX : g ∈ normalizer (X : Set G)) {Y : Subgroup G}
    (hY : V ≤ Y ∧ Y ≤ X ∧ ElemAbMod V Y) :
    V ≤ Y.map (MulAut.conj g).toMonoidHom ∧ Y.map (MulAut.conj g).toMonoidHom ≤ X ∧
      ElemAbMod V (Y.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hVY, hYX, hab1, hab2⟩ := hY
  have hgV' : g⁻¹ ∈ normalizer (V : Set G) := inv_mem hgV
  refine ⟨fun v hv => ?_, ?_, ⟨?_, ?_⟩⟩
  · rw [sec38b_mem_map_conj]
    have := (mem_normalizer_iff.1 hgV' v).1 hv
    rw [inv_inv] at this
    exact hVY this
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.1 hgX y).1 (hYX hy)
  · rintro _ ⟨y, hy, rfl⟩
    have := (mem_normalizer_iff.1 hgV (y * y)).1 (hab1 y hy)
    simpa [MulAut.conj_apply, mul_assoc] using this
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    have := (mem_normalizer_iff.1 hgV _).1 (hab2 y hy y' hy')
    have e : ⁅(MulAut.conj g).toMonoidHom y, (MulAut.conj g).toMonoidHom y'⁆ =
        g * ⁅y, y'⁆ * g⁻¹ := by
      rw [← map_commutatorElement]; rfl
    rw [e]
    exact this

theorem sec38b_maximal_conj {G : Type*} [Group G] {P : Subgroup G → Prop} {g : G}
    (hP : ∀ Y, P Y → P (Y.map (MulAut.conj g).toMonoidHom))
    (hP' : ∀ Y, P Y → P (Y.map (MulAut.conj g⁻¹).toMonoidHom))
    {Y : Subgroup G} (hY : Maximal P Y) : Maximal P (Y.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨hP Y hY.1, fun Z hZ hle => ?_⟩
  have h1 : Y ≤ Z.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro y hy
    rw [sec38b_mem_map_conj, inv_inv]
    exact hle ⟨y, hy, rfl⟩
  have h2 : Z.map (MulAut.conj g⁻¹).toMonoidHom ≤ Y := hY.2 (hP' Z hZ) h1
  intro z hz
  rw [sec38b_mem_map_conj]
  have := h2 (show g⁻¹ * z * g⁻¹⁻¹ ∈ Z.map (MulAut.conj g⁻¹).toMonoidHom from ⟨z, hz, rfl⟩)
  rwa [inv_inv] at this

theorem sec38b_odd_card_closure {H : Type*} [Group H] [Finite H] (S : Set H)
    (hcomm : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s)) :
    Odd (Nat.card (Subgroup.closure S)) := by
  have hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx y hy
    refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y) ?_ ?_ ?_ ?_ ?_ ?_ ?_
      hx hy
    · exact fun x y hx hy => hcomm x hx y hy
    · exact fun x _ => Commute.one_left x
    · exact fun x _ => Commute.one_right x
    · exact fun x y z _ _ _ h1 h2 => Commute.mul_left h1 h2
    · exact fun y z x _ _ _ h1 h2 => Commute.mul_right h1 h2
    · exact fun x y _ _ h => h.inv_left
    · exact fun x y _ _ h => h.inv_right
  have hall : ∀ x ∈ Subgroup.closure S, ∃ m, Odd m ∧ x ^ m = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => ∃ m, Odd m ∧ x ^ m = 1) ?_ ?_ ?_ ?_ hx
    · intro s hs
      exact ⟨orderOf s, hodd s hs, pow_orderOf_eq_one s⟩
    · exact ⟨1, odd_one, by simp⟩
    · intro x y hx hy ⟨m, hm, hxm⟩ ⟨n, hn, hyn⟩
      refine ⟨m * n, hm.mul hn, ?_⟩
      rw [(hc x hx y hy).mul_pow, pow_mul, hxm, one_pow, mul_comm m n, pow_mul, hyn, one_pow,
        one_mul]
    · intro x hx ⟨m, hm, hxm⟩
      exact ⟨m, hm, by rw [inv_pow, hxm, inv_one]⟩
  by_contra hne
  have h2 : 2 ∣ Nat.card (Subgroup.closure S) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.closure S)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.closure S) 2 h2
  obtain ⟨m, hm, hxm⟩ := hall x x.2
  have hxm' : x ^ m = 1 := Subtype.ext (by simpa using hxm)
  have : orderOf x ∣ m := orderOf_dvd_of_pow_eq_one hxm'
  rw [hx] at this
  exact (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 this)

theorem sec38b_le_oddCore_of_commuting_conjugates {K : Type*} [Group K] [Finite K]
    (Q : Subgroup K) (hodd : ∀ q ∈ Q, Odd (orderOf q))
    (hcomm : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ g g' : K, Commute (g * q * g⁻¹) (g' * q' * g'⁻¹)) :
    Q ≤ CFSG.Open.standardComponentOddCore K := by
  set S : Set K := {x | ∃ g : K, ∃ q ∈ Q, x = g * q * g⁻¹} with hS
  have hSodd : ∀ s ∈ S, Odd (orderOf s) := by
    rintro _ ⟨g, q, hq, rfl⟩
    have : orderOf (g * q * g⁻¹) = orderOf q := MulEquiv.orderOf_eq (MulAut.conj g) q
    rw [this]
    exact hodd q hq
  have hScomm : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    rintro _ ⟨g, q, hq, rfl⟩ _ ⟨g', q', hq', rfl⟩
    exact hcomm q hq q' hq' g g'
  have hRodd := sec38b_odd_card_closure S hScomm hSodd
  haveI : (Subgroup.closure S).Normal := ⟨fun x hx g => by
    refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure S) ?_ ?_ ?_ ?_
      hx
    · rintro _ ⟨g', q, hq, rfl⟩
      exact subset_closure ⟨g * g', q, hq, by group⟩
    · simp
    · intro x y _ _ hx hy
      have := mul_mem hx hy
      rwa [show g * x * g⁻¹ * (g * y * g⁻¹) = g * (x * y) * g⁻¹ by group] at this
    · intro x _ hx
      have := inv_mem hx
      rwa [show (g * x * g⁻¹)⁻¹ = g * x⁻¹ * g⁻¹ by group] at this⟩
  have hle : Subgroup.closure S ≤ CFSG.Open.standardComponentOddCore K :=
    le_sSup ⟨inferInstance, hRodd⟩
  have hQ : Q ≤ Subgroup.closure S := fun q hq => subset_closure ⟨1, q, hq, by simp⟩
  exact hQ.trans hle

theorem sec38b_eq_bot_of_commuting_conjugates {K : Type*} [Group K] [Finite K]
    (hK : CFSG.Open.standardComponentOddCore K = ⊥) (Q : Subgroup K)
    (hodd : ∀ q ∈ Q, Odd (orderOf q))
    (hcomm : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ g g' : K, Commute (g * q * g⁻¹) (g' * q' * g'⁻¹)) :
    Q = ⊥ := by
  have := sec38b_le_oddCore_of_commuting_conjugates Q hodd hcomm
  rw [hK] at this
  exact eq_bot_iff.2 this

end Generic

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec38b_t_notMem_E (hp : d.CaseHyp) : d.t ∉ d.E := by
  intro htE
  have htB : d.t ∈ d.B₂ := mem_sup_left (mem_zpowers d.t)
  have : d.t ∈ d.E ⊓ d.B₂ := ⟨htE, htB⟩
  rw [hp.hyp.E_inf_B₂ hp.gms] at this
  exact hp.hyp.t_not_mem_L (d.P_le_L (d.A₂_le_P this))

theorem sec38b_center_N₂ (d : Data G h) :
    ∀ z ∈ center ↥d.N₂, ∀ k : ℕ, z ^ 2 ^ k = 1 → z = 1 := by
  intro z hz k hk
  have hzN : (z : G) ∈ d.N₂ := z.2
  have hI₂ : (z : G) ∈ d.I₂ := d.mem_I₂_of_comm_N₂ hzN fun n hn =>
    congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨n, hn⟩).symm
  have hI : (z : G) ∈ d.I := d.pull_mono (torusEq_le _) hI₂
  set zI : ↥d.I := ⟨z, hI⟩ with hzI
  have h1 : orderOf zI ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
    simpa using congrArg Subtype.val hk))
  have h2 : orderOf zI ∣ Nat.card ↥d.I := orderOf_dvd_natCard zI
  have hcop : Nat.Coprime (2 ^ k) (Nat.card ↥d.I) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 d.odd_card_I)
  have h3 : orderOf zI = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : zI = 1 := orderOf_eq_one_iff.1 h3
  have h5 : (z : G) = 1 := congrArg Subtype.val h4
  exact Subtype.ext h5

theorem sec38b_E_inf_N₂ (hp : d.CaseHyp) : d.E ⊓ d.N₂ = ⊥ := by
  have hq : CFSG.Open.IsQuasisimple ↥d.N₂ :=
    (hp.hyp.quasisimple_lieModel_N₂ (X := ↥d.N₂) ⟨MulEquiv.refl _⟩).1
  set Y : Subgroup ↥d.N₂ := (d.E ⊓ d.N₂).subgroupOf d.N₂ with hY
  haveI hYn : Y.Normal := ⟨fun y hy n => by
    rw [hY, mem_subgroupOf] at hy ⊢
    refine ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 (d.N₂_le_normalizer_E n.2) y).1 hy.1
      simpa using this
    · exact (n * y * n⁻¹).2⟩
  have hYp : IsPGroup 2 Y :=
    ((hp.hyp.isPGroup_E hp.gms).to_le (inf_le_left : d.E ⊓ d.N₂ ≤ d.E)).of_equiv
      (subgroupOfEquivOfLe (inf_le_right : d.E ⊓ d.N₂ ≤ d.N₂)).symm
  have hY1 := sec38b_normal_two_group_eq_bot hq (sec38b_center_N₂ d) Y hYp
  refine eq_bot_iff.2 fun x hx => ?_
  have hxY : (⟨x, hx.2⟩ : ↥d.N₂) ∈ Y := mem_subgroupOf.2 hx
  rw [hY1, mem_bot] at hxY
  exact congrArg Subtype.val hxY

theorem sec38b_barEquiv (hp : d.CaseHyp) : Nonempty (↥(bar d.E d.N₂) ≃* ↥d.N₂) := by
  set φ : ↥d.N₂ →* Bar d.E :=
    (proj d.E).comp (Subgroup.inclusion (d.N₂_le_normalizer_E)) with hφ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro n hn
    have h1 : (n : G) ∈ d.E :=
      (proj_eq_one_iff (A := d.E) (x := Subgroup.inclusion d.N₂_le_normalizer_E n)).1 hn
    have h2 : (n : G) ∈ d.E ⊓ d.N₂ := ⟨h1, n.2⟩
    rw [sec38b_E_inf_N₂ hp, mem_bot] at h2
    exact Subtype.ext h2
  have hrange : bar d.E d.N₂ = φ.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨Subgroup.inclusion d.N₂_le_normalizer_E n, n.2, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hinj).symm⟩

theorem sec38b_quasisimple_model (hp : d.CaseHyp) :
    CFSG.Open.IsQuasisimple ↥(bar d.E d.N₂) ∧
      LieModel (↥(bar d.E d.N₂) ⧸ center ↥(bar d.E d.N₂)) .PSU 3 2 f :=
  hp.hyp.quasisimple_lieModel_N₂ (X := ↥(bar d.E d.N₂)) (sec38b_barEquiv hp)

theorem sec38b_normalizer_E_ne_top (hp : d.CaseHyp) : normalizer (d.E : Set G) ≠ ⊤ := by
  intro htop
  haveI hE : d.E.Normal := normalizer_eq_top_iff.1 htop
  haveI hsimple : IsSimpleGroup G := hp.hyp.setting.std.simple
  have hE2 := hp.hyp.isPGroup_E hp.gms
  have hcard := hp.hyp.card_E hp.gms
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal d.E with hb | ht
  · rw [hb, Subgroup.card_bot] at hcard
    have : (1 : ℕ) < (2 ^ f) ^ 14 := by
      have : 1 < 2 ^ f := Nat.one_lt_two_pow (by have := hp.hyp.two_le; omega)
      exact Nat.one_lt_pow (by norm_num) this
    omega
  · have hG2 : IsPGroup 2 G := by
      rw [ht] at hE2
      exact hE2.of_equiv Subgroup.topEquiv
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Nontrivial G := hsimple.toNontrivial
    haveI : Nontrivial (center G) := hG2.center_nontrivial
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with hc | hc
    · obtain ⟨z, hz⟩ := exists_ne (1 : center G)
      exact hz (Subtype.ext (Subgroup.mem_bot.1 (hc.le z.2)))
    · obtain ⟨a, b, hab⟩ := hp.hyp.setting.std.nonab
      have : a ∈ center G := by rw [hc]; exact mem_top a
      exact hab ((Subgroup.mem_center_iff.1 this b).symm)

theorem sec38b_kgroup (hp : d.CaseHyp) : CFSG.SectionRank.IsKGroupCat (Bar d.E) :=
  (CFSG.QuasithinUnique.isKGroupCat_of_kProper hp.hyp.setting.std.kProper
    (sec38b_normalizer_E_ne_top hp)).quotient _

theorem sec38b_order_two (hp : d.CaseHyp) (ht : d.t ∈ normalizer (d.E : Set G)) :
    orderOf (proj d.E ⟨d.t, ht⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : d.t ^ 2 = 1 := by
    have := pow_orderOf_eq_one d.t
    rwa [hp.hyp.t_two] at this
  refine orderOf_eq_prime ?_ ?_
  · rw [← map_pow]
    have : (⟨d.t, ht⟩ : normalizer (d.E : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  · intro h1
    exact sec38b_t_notMem_E hp ((proj_eq_one_iff (A := d.E)).1 h1)

theorem sec38b_centralizes (hp : d.CaseHyp) (ht : d.t ∈ normalizer (d.E : Set G)) :
    proj d.E ⟨d.t, ht⟩ ∈ centralizer ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) := by
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyC : (y : G) ∈ centralizer ({d.t} : Set G) := hp.hyp.N₂_le_C hy
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (mem_centralizer_singleton_iff.1 hyC)

theorem sec38b_N₂_le_normalizer_A₂ (hd : d.Hyp) : d.N₂ ≤ normalizer (d.A₂ : Set G) := by
  intro n hn
  have hK := hd.N₂_le_K₀ hn
  exact CFSG.RankThree.PartOne.U5K.Hyp.mem_normalizer_of_conj_le fun a ha =>
    hd.conj_mem_A₂ hK.1.1 hK.2 ha

theorem sec38b_exists_conj (hd : d.Hyp) {c : G}
    (hc : c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G)) {n : G} (hn : n ∈ d.N₂) :
    ∃ a ∈ d.A₂, ∃ n' ∈ d.N₂, c * n * c⁻¹ = a * n' := by
  have hcB := hc.1
  have hct := hc.2
  have hcL := hd.centralizer_le_normalizer hct
  have hcZ : c ∈ normalizer (d.ZtP : Set G) := by
    rw [← hd.centerIn_B₂]
    exact mem_normalizer_centerIn hcB
  have hmem := hd.conj_N₂_mem_A₂_sup_N₂ hcZ hcL hn
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left d.A₂ d.N₂
    (sec38b_N₂_le_normalizer_A₂ hd)] at hmem
  obtain ⟨a, ha, n', hn', e⟩ := hmem
  exact ⟨a, ha, n', hn', e.symm⟩

theorem sec38b_mem_normalizer_VB₂ (hp : d.CaseHyp) (ha : d.Sec38a1) {g : G}
    (hg : g ∈ normalizer (d.E : Set G)) (hgt : d.t * g⁻¹ * d.t * g ∈ d.E) :
    g ∈ normalizer ((d.V ⊔ d.B₂ : Subgroup G) : Set G) := by
  have htt : d.t * d.t = 1 := by
    have := pow_orderOf_eq_one d.t
    rwa [hp.hyp.t_two, pow_two] at this
  set X : Subgroup G := d.E ⊔ zpowers d.t with hX
  have hgX : g ∈ normalizer (X : Set G) := by
    have h1 : ∀ x ∈ X, g⁻¹ * x * g⁻¹⁻¹ ∈ X := by
      intro x hx
      have hle : X ≤ X.comap (MulAut.conj g⁻¹).toMonoidHom := by
        refine sup_le ?_ ?_
        · intro e he
          show g⁻¹ * e * g⁻¹⁻¹ ∈ X
          have := (mem_normalizer_iff.1 (inv_mem hg) e).1 he
          exact mem_sup_left this
        · refine zpowers_le.2 ?_
          show g⁻¹ * d.t * g⁻¹⁻¹ ∈ X
          rw [inv_inv]
          have e1 : g⁻¹ * d.t * g = d.t * (d.t * g⁻¹ * d.t * g) := by
            calc g⁻¹ * d.t * g = (d.t * d.t) * g⁻¹ * d.t * g := by rw [htt, one_mul]
              _ = d.t * (d.t * g⁻¹ * d.t * g) := by group
          rw [e1]
          exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left hgt)
      exact hle hx
    have := CFSG.RankThree.PartOne.U5K.Hyp.mem_normalizer_of_conj_le h1
    simpa using inv_mem this
  have hgV : g ∈ normalizer (d.V : Set G) := by
    have := mem_normalizer_centerIn hg
    rwa [hp.hyp.centerIn_E hp.gms] at this
  have hmax : Maximal (fun Y : Subgroup G => d.V ≤ Y ∧ Y ≤ X ∧ ElemAbMod d.V Y) (d.V ⊔ d.B₂) :=
    (ha.maximal _).2 (Or.inr rfl)
  have hmax' := sec38b_maximal_conj (g := g)
    (P := fun Y : Subgroup G => d.V ≤ Y ∧ Y ≤ X ∧ ElemAbMod d.V Y)
    (fun Y hY => sec38b_conj_stable hgV hgX hY)
    (fun Y hY => sec38b_conj_stable (inv_mem hgV) (inv_mem hgX) hY) hmax
  have htB : d.t ∈ d.V ⊔ d.B₂ := mem_sup_right (mem_sup_left (mem_zpowers d.t))
  rcases (ha.maximal _).1 hmax' with hE | hVB
  · exfalso
    have h1 : g * d.t * g⁻¹ ∈ (d.V ⊔ d.B₂).map (MulAut.conj g).toMonoidHom := ⟨d.t, htB, rfl⟩
    rw [hE] at h1
    exact sec38b_t_notMem_E hp ((mem_normalizer_iff.1 hg d.t).2 h1)
  · refine mem_normalizer_iff.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · rw [← hVB]
      exact ⟨x, hx, rfl⟩
    · rw [← hVB, sec38b_mem_map_conj] at hx
      simpa [mul_assoc] using hx

theorem sec38b_comm_of_mem_centralizer (hp : d.CaseHyp)
    (ht : d.t ∈ normalizer (d.E : Set G)) {γ : normalizer (d.E : Set G)}
    (hγ : proj d.E γ ∈ centralizer ({proj d.E ⟨d.t, ht⟩} : Set (Bar d.E))) :
    d.t * (γ : G)⁻¹ * d.t * (γ : G) ∈ d.E := by
  have htt : d.t * d.t = 1 := by
    have := pow_orderOf_eq_one d.t
    rwa [hp.hyp.t_two, pow_two] at this
  have h1 := mem_centralizer_singleton_iff.1 hγ
  rw [← map_mul, ← map_mul, proj_eq_proj_iff] at h1
  have e : ((γ * ⟨d.t, ht⟩ : normalizer (d.E : Set G)) : G)⁻¹ *
      ((⟨d.t, ht⟩ * γ : normalizer (d.E : Set G)) : G) = d.t * (γ : G)⁻¹ * d.t * (γ : G) := by
    change ((γ : G) * d.t)⁻¹ * (d.t * (γ : G)) = _
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right htt]
    group
  rwa [e] at h1

theorem sec38b_conj_N₂ (hp : d.CaseHyp) (ha : d.Sec38a1) {g : G}
    (hg : g ∈ normalizer (d.E : Set G)) (hgt : d.t * g⁻¹ * d.t * g ∈ d.E) {n : G}
    (hn : n ∈ d.N₂) :
    ∃ e ∈ d.E, ∃ c ∈ normalizer (d.B₂ : Set G) ⊓ centralizer ({d.t} : Set G),
      ∃ a ∈ d.A₂, ∃ n' ∈ d.N₂, g = e * c ∧ c * n * c⁻¹ = a * n' := by
  obtain ⟨e, he, c, hc, hgec⟩ :=
    (hp.hyp.sec3_6 hp.gms).1 g (sec38b_mem_normalizer_VB₂ hp ha hg hgt)
  obtain ⟨a, haA, n', hn', hcn⟩ := sec38b_exists_conj hp.hyp hc hn
  exact ⟨e, he, c, hc, a, haA, n', hn', hgec, hcn⟩

theorem sec38b_normal (hp : d.CaseHyp) (ha : d.Sec38a1)
    (ht : d.t ∈ normalizer (d.E : Set G)) :
    ((bar d.E d.N₂).subgroupOf
      (centralizer ({proj d.E ⟨d.t, ht⟩} : Set (Bar d.E)))).Normal := by
  refine ⟨fun x hx y => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨xn, hxn, hxe⟩ := hx
  obtain ⟨γ, hγ⟩ := proj_surjective (A := d.E) (y : Bar d.E)
  have hycent : proj d.E γ ∈ centralizer ({proj d.E ⟨d.t, ht⟩} : Set (Bar d.E)) := by
    rw [hγ]; exact y.2
  have hcomm := sec38b_comm_of_mem_centralizer hp ht hycent
  obtain ⟨e, he, c, hc, a, haA, n', hn', hgec, hcn⟩ := sec38b_conj_N₂ hp ha γ.2 hcomm
    (n := (xn : G)) hxn
  have hn'N : n' ∈ normalizer (d.E : Set G) := d.N₂_le_normalizer_E hn'
  have haE : a ∈ d.E := hp.hyp.A₂_le_E hp.gms haA
  have key : proj d.E (γ * xn * γ⁻¹) = proj d.E ⟨n', hn'N⟩ := by
    rw [proj_eq_proj_iff]
    change ((γ : G) * (xn : G) * (γ : G)⁻¹)⁻¹ * n' ∈ d.E
    have e1 : (γ : G) * (xn : G) * (γ : G)⁻¹ = e * (c * (xn : G) * c⁻¹) * e⁻¹ := by
      rw [hgec]; group
    rw [e1, hcn]
    have e2 : (e * (a * n') * e⁻¹)⁻¹ * n' = e * (n'⁻¹ * (a⁻¹ * e⁻¹) * n'⁻¹⁻¹) := by group
    rw [e2]
    refine mul_mem he ?_
    exact (mem_normalizer_iff.1 (inv_mem hn'N) _).1 (mul_mem (inv_mem haE) (inv_mem he))
  change (y : Bar d.E) * (x : Bar d.E) * (y : Bar d.E)⁻¹ ∈ bar d.E d.N₂
  rw [← hγ, ← hxe, ← map_inv, ← map_mul, ← map_mul, key]
  exact proj_mem_bar hn'

theorem sec38b_proj_mem_zpowers (ht : d.t ∈ normalizer (d.E : Set G))
    {x : normalizer (d.E : Set G)} (hx : (x : G) ∈ d.E ⊔ zpowers d.t) :
    proj d.E x ∈ zpowers (proj d.E ⟨d.t, ht⟩) := by
  have hzt : zpowers d.t ≤ normalizer (d.E : Set G) := zpowers_le.2 ht
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left d.E (zpowers d.t) hzt] at hx
  obtain ⟨e', he', w, hw, hxe⟩ := hx
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hw
  refine ⟨i, ?_⟩
  show (proj d.E ⟨d.t, ht⟩) ^ i = proj d.E x
  rw [← map_zpow]
  symm
  rw [proj_eq_proj_iff]
  change (x : G)⁻¹ * d.t ^ i ∈ d.E
  rw [← hxe]
  have hti : d.t ^ i ∈ normalizer (d.E : Set G) := hzt (zpow_mem (mem_zpowers d.t) i)
  have e : (e' * d.t ^ i)⁻¹ * d.t ^ i = (d.t ^ i)⁻¹ * e'⁻¹ * (d.t ^ i)⁻¹⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 (inv_mem hti) _).1 (inv_mem he')

theorem sec38b_rank_local (hp : d.CaseHyp) (ha : d.Sec38a1)
    (ht : d.t ∈ normalizer (d.E : Set G)) :
    ∀ Q : Subgroup (Bar d.E),
      Q ≤ centralizer ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) ⊓
        centralizer ({proj d.E ⟨d.t, ht⟩} : Set (Bar d.E)) →
      IsPGroup 2 Q → Q ≤ zpowers (proj d.E ⟨d.t, ht⟩) := by
  intro Q hQ hQ2 x hx
  obtain ⟨γ, rfl⟩ := proj_surjective (A := d.E) x
  have hxA := (hQ hx).1
  have hxt := (hQ hx).2
  have hcomm := sec38b_comm_of_mem_centralizer hp ht hxt
  obtain ⟨e, he, c, hc, hgec⟩ := (hp.hyp.sec3_6 hp.gms).1 (γ : G)
    (sec38b_mem_normalizer_VB₂ hp ha γ.2 hcomm)
  have hcN : c ∈ normalizer (d.E : Set G) :=
    (hp.hyp.sec3_6 hp.gms).2.2.1 ((hp.hyp.sec3_6 hp.gms).2.1 (mem_sup_right hc))
  have hproj : proj d.E γ = proj d.E ⟨c, hcN⟩ := by
    rw [proj_eq_proj_iff]
    change (γ : G)⁻¹ * c ∈ d.E
    rw [hgec]
    have e1 : (e * c)⁻¹ * c = c⁻¹ * e⁻¹ * c⁻¹⁻¹ := by group
    rw [e1]
    exact (mem_normalizer_iff.1 (inv_mem hcN) _).1 (inv_mem he)
  obtain ⟨k, hk⟩ := hQ2 ⟨proj d.E γ, hx⟩
  have hk' : (proj d.E γ) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hck : c ^ 2 ^ k ∈ d.E := by
    rw [hproj, ← map_pow] at hk'
    exact (proj_eq_one_iff (A := d.E)).1 hk'
  obtain ⟨m, hm⟩ := (hp.hyp.isPGroup_E hp.gms) ⟨c ^ 2 ^ k, hck⟩
  have hcm : c ^ 2 ^ (k + m) = 1 := by
    rw [pow_add, pow_mul]
    simpa using congrArg Subtype.val hm
  have hcN₂ : ∀ n ∈ d.N₂, c * n * c⁻¹ * n⁻¹ ∈ d.A₂ := by
    intro n hn
    obtain ⟨a, haA, n', hn', hcn⟩ := sec38b_exists_conj hp.hyp hc hn
    have hnN : n ∈ normalizer (d.E : Set G) := d.N₂_le_normalizer_E hn
    have hn'N : n' ∈ normalizer (d.E : Set G) := d.N₂_le_normalizer_E hn'
    have haE : a ∈ d.E := hp.hyp.A₂_le_E hp.gms haA
    have h1 := (mem_centralizer_iff.1 hxA (proj d.E ⟨n, hnN⟩) (proj_mem_bar hn)).symm
    rw [hproj, ← map_mul, ← map_mul, proj_eq_proj_iff] at h1
    have h2 : n⁻¹ * c⁻¹ * n * c ∈ d.E := by
      have e : ((⟨c, hcN⟩ * ⟨n, hnN⟩ : normalizer (d.E : Set G)) : G)⁻¹ *
          ((⟨n, hnN⟩ * ⟨c, hcN⟩ : normalizer (d.E : Set G)) : G) = n⁻¹ * c⁻¹ * n * c := by
        change (c * n)⁻¹ * (n * c) = _
        group
      rwa [e] at h1
    have h3 : (c * n * c⁻¹)⁻¹ * n ∈ d.E := by
      have h3' := (mem_normalizer_iff.1 hcN _).1 h2
      have e : c * (n⁻¹ * c⁻¹ * n * c) * c⁻¹ = (c * n * c⁻¹)⁻¹ * n := by group
      rwa [e] at h3'
    rw [hcn] at h3
    have h4 : n'⁻¹ * n ∈ d.E := by
      have hconj : n'⁻¹ * a⁻¹ * n'⁻¹⁻¹ ∈ d.E :=
        (mem_normalizer_iff.1 (inv_mem hn'N) _).1 (inv_mem haE)
      have h4' := mul_mem (inv_mem hconj) h3
      have e : (n'⁻¹ * a⁻¹ * n'⁻¹⁻¹)⁻¹ * ((a * n')⁻¹ * n) = n'⁻¹ * n := by group
      rwa [e] at h4'
    have h5 : n'⁻¹ * n ∈ d.E ⊓ d.N₂ := Subgroup.mem_inf.2 ⟨h4, mul_mem (inv_mem hn') hn⟩
    rw [sec38b_E_inf_N₂ hp, mem_bot] at h5
    have hn'n : n' = n := inv_mul_eq_one.1 h5
    rw [hcn, hn'n, mul_inv_cancel_right]
    exact haA
  have hcB : c ∈ d.B₂ := hp.hyp.mem_B₂_of_commutator_N₂_mem_A₂ hc hcN₂ hcm
  rw [hproj]
  exact sec38b_proj_mem_zpowers ht (x := ⟨c, hcN⟩)
    ((show d.B₂ ≤ d.E ⊔ zpowers d.t from sup_le le_sup_right
      ((hp.hyp.A₂_le_E hp.gms).trans le_sup_left)) hcB)

theorem sec38b_t_mem (hp : d.CaseHyp) : d.t ∈ normalizer (d.E : Set G) :=
  hp.hyp.normalizer_B₄_le_normalizer_E hp.gms (le_normalizer hp.hyp.t_mem_B₄)

theorem sec38b_rank (hp : d.CaseHyp) (ha : d.Sec38a1)
    (ht : d.t ∈ normalizer (d.E : Set G)) :
    ∀ P : Subgroup (Bar d.E),
      P ≤ centralizer ((bar d.E d.N₂ : Subgroup (Bar d.E)) : Set (Bar d.E)) → IsPGroup 2 P →
        Nat.card P ≤ 2 :=
  sec38b_card_le_two (sec38b_order_two hp ht) (sec38b_centralizes hp ht)
    (sec38b_rank_local hp ha ht)

theorem sec38b_center_odd (d : Data G h) (hp : d.CaseHyp) :
    ∀ a ∈ center ↥(bar d.E d.N₂), Odd (orderOf a) := by
  intro a ha
  obtain ⟨e⟩ := sec38b_barEquiv hp
  have hea : e a ∈ center ↥d.N₂ := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 ha x]
  rw [← MulEquiv.orderOf_eq e a]
  by_contra hne
  have h2 : 2 ∣ orderOf (e a) := by
    rcases Nat.even_or_odd (orderOf (e a)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hne
  obtain ⟨m, hm⟩ := h2
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (orderOf_pos (e a)).ne' (by simpa using hm)
  have hdvd : m ∣ orderOf (e a) := ⟨2, by rw [hm]; ring⟩
  have hw : orderOf ((e a) ^ m) = 2 := by
    rw [orderOf_pow_of_dvd hm0 hdvd, hm]
    exact Nat.mul_div_cancel 2 (Nat.pos_of_ne_zero hm0)
  have hwc : (e a) ^ m ∈ center ↥d.N₂ := pow_mem hea m
  have hw2 : ((e a) ^ m) ^ 2 = 1 := by
    have := pow_orderOf_eq_one ((e a) ^ m)
    rwa [hw] at this
  have hw1 := sec38b_center_N₂ d _ hwc 1 (by simpa using hw2)
  rw [hw1, orderOf_one] at hw
  omega

theorem sec38b_centre_le_of_normal (hp : d.CaseHyp)
    (hN : ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal) :
    (center ↥(bar d.E d.N₂)).map (bar d.E d.N₂).subtype ≤ OE d := by
  set A : Subgroup (Bar d.E) := bar d.E d.N₂ with hA
  set θ := QuotientGroup.mk' (OE d) with hθ
  set Q : Subgroup (Bar d.E ⧸ OE d) := ((center ↥A).map A.subtype).map θ with hQ
  have hodd : ∀ q ∈ Q, Odd (orderOf q) := by
    rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    have h1 : orderOf (a : Bar d.E) = orderOf a := Subgroup.orderOf_coe a
    exact Odd.of_dvd_nat (h1 ▸ sec38b_center_odd d hp a ha) (orderOf_map_dvd θ (a : Bar d.E))
  have hcomm : ∀ q ∈ Q, ∀ q' ∈ Q, ∀ g g' : Bar d.E ⧸ OE d,
      Commute (g * q * g⁻¹) (g' * q' * g'⁻¹) := by
    intro q hq q' hq' g g'
    obtain ⟨_, ⟨a, ha, rfl⟩, rfl⟩ := hq
    obtain ⟨_, ⟨a', ha', rfl⟩, rfl⟩ := hq'
    have hq'A : θ (a' : Bar d.E) ∈ A.map θ := ⟨_, a'.2, rfl⟩
    have hw : g' * θ (a' : Bar d.E) * g'⁻¹ ∈ A.map θ := hN.conj_mem _ hq'A g'
    have hw2 : g⁻¹ * (g' * θ (a' : Bar d.E) * g'⁻¹) * g ∈ A.map θ := by
      have := hN.conj_mem _ hw g⁻¹
      simpa using this
    obtain ⟨b, hb, hbe⟩ := hw2
    have hab : θ (a : Bar d.E) * θ b = θ b * θ (a : Bar d.E) := by
      rw [← map_mul, ← map_mul]
      have := Subgroup.mem_center_iff.1 ha ⟨b, hb⟩
      exact congrArg θ (congrArg Subtype.val this.symm)
    change θ (a : Bar d.E) * θ b = θ b * θ (a : Bar d.E) at hab
    rw [hbe] at hab
    show g * θ (a : Bar d.E) * g⁻¹ * (g' * θ (a' : Bar d.E) * g'⁻¹) =
      g' * θ (a' : Bar d.E) * g'⁻¹ * (g * θ (a : Bar d.E) * g⁻¹)
    calc g * θ (a : Bar d.E) * g⁻¹ * (g' * θ (a' : Bar d.E) * g'⁻¹)
        = g * (θ (a : Bar d.E) * (g⁻¹ * (g' * θ (a' : Bar d.E) * g'⁻¹) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (g' * θ (a' : Bar d.E) * g'⁻¹) * g) * θ (a : Bar d.E)) * g⁻¹ := by
          rw [hab]
      _ = g' * θ (a' : Bar d.E) * g'⁻¹ * (g * θ (a : Bar d.E) * g⁻¹) := by group
  have hK := GMSK.standardComponentOddCore_quotient_eq_bot (Bar d.E)
  have hQbot := sec38b_eq_bot_of_commuting_conjugates hK Q hodd hcomm
  rintro _ ⟨a, ha, rfl⟩
  have hmem : θ (a : Bar d.E) ∈ Q := ⟨_, ⟨a, ha, rfl⟩, rfl⟩
  rw [hQbot, Subgroup.mem_bot] at hmem
  exact (QuotientGroup.eq_one_iff _).1 hmem

theorem sec38b_centre_le_of_clause (hp : d.CaseHyp) (ha : d.Sec38a)
    (hz : GMSK.GMSUnitaryCentreStatement) :
    (center ↥(bar d.E d.N₂)).map (bar d.E d.N₂).subtype ≤ OE d := by
  by_cases hN : ((bar d.E d.N₂).map (QuotientGroup.mk' (OE d))).Normal
  · exact sec38b_centre_le_of_normal hp hN
  · have ht := sec38b_t_mem hp
    obtain ⟨hq, hm⟩ := sec38b_quasisimple_model hp
    exact hz (Bar d.E) (sec38b_kgroup hp) f (bar d.E d.N₂) (proj d.E ⟨d.t, ht⟩) hq hm
      (sec38b_order_two hp ht) (sec38b_centralizes hp ht) (sec38b_normal hp ha.toSec38a1 ht)
      (sec38b_rank hp ha.toSec38a1 ht) hN

end Data

section Certified

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

theorem sec38b_centre_le (hp : d.CaseHyp) (ha : d.Sec38a) :
    (center ↥(bar d.E d.N₂)).map (bar d.E d.N₂).subtype ≤ OE d :=
  sec38b_centre_le_of_clause hp ha GMSK.gmsUnitaryCentre

theorem sec38_input (hp : d.CaseHyp) (ha : d.Sec38a) : d.Sec38Input :=
  ⟨sec38b_t_mem hp, sec38b_kgroup hp, (sec38b_quasisimple_model hp).1,
    (sec38b_quasisimple_model hp).2, sec38b_centre_le hp ha,
    sec38b_order_two hp (sec38b_t_mem hp), sec38b_centralizes hp (sec38b_t_mem hp),
    sec38b_normal hp ha.toSec38a1 (sec38b_t_mem hp),
    sec38b_rank hp ha.toSec38a1 (sec38b_t_mem hp)⟩

end Data

namespace CaseBParts

theorem sec38Input : Sec38InputStatement :=
  fun _ _ _ _ _ _ _ _ hp ha => Data.sec38_input hp ha

end CaseBParts

end Certified

end CFSG.LocalAnalysis.EvenBN.U5
