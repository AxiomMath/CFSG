module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.XbarSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.A7Transport
public import CFSG.Open.FusionDefs

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup CFSG.Open

section OddCore

theorem natCard_fusionOddCore_odd (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) := by
  have h : fusionOddCore X = CFSG.pPrimeCore 2 X := by
    unfold fusionOddCore CFSG.pPrimeCore
    congr 1
    ext K
    simp [Nat.coprime_two_left]
  rw [h]
  exact Nat.coprime_two_left.1 (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

theorem le_fusionOddCore_of_odd {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ fusionOddCore X :=
  le_sSup ⟨inferInstance, hN⟩

theorem fusionOddCore_eq_bot_of_equiv {X Y : Type*} [Group X] [Finite X] [Group Y]
    (e : X ≃* Y) (h : fusionOddCore Y = ⊥) : fusionOddCore X = ⊥ := by
  have hN : ((fusionOddCore X).map e.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have hodd : Odd (Nat.card ((fusionOddCore X).map e.toMonoidHom)) := by
    rw [Subgroup.card_map_of_injective e.injective]
    exact natCard_fusionOddCore_odd X
  have hle := le_fusionOddCore_of_odd (N := (fusionOddCore X).map e.toMonoidHom) hodd
  rw [h, le_bot_iff] at hle
  rw [eq_bot_iff]
  intro x hx
  have h1 : e.toMonoidHom x ∈ (fusionOddCore X).map e.toMonoidHom := ⟨x, hx, rfl⟩
  rw [hle, mem_bot] at h1
  exact mem_bot.2 ((MulEquiv.map_eq_one_iff e).1 h1)

theorem even_natCard_alternatingGroup_seven : Even (Nat.card (alternatingGroup (Fin 7))) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp only [Fintype.card_fin]
  exact ⟨1260, by decide⟩

theorem fusionOddCore_prod_eq_bot_of_simple {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hA : Even (Nat.card A)) : fusionOddCore (Multiplicative (ZMod 2) × A) = ⊥ := by
  have hodd : Odd (Nat.card (fusionOddCore (Multiplicative (ZMod 2) × A))) :=
    natCard_fusionOddCore_odd _
  set N := fusionOddCore (Multiplicative (ZMod 2) × A) with hN
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hab
  have hord : Odd (orderOf (a, b)) :=
    Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard N hab)
  obtain ⟨k, hk⟩ := hord
  have habk : (a, b) ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one _
  have ha2 : ∀ x : Multiplicative (ZMod 2), x ^ 2 = 1 := by decide
  have hak : a ^ (2 * k + 1) = 1 := by simpa [Prod.pow_def] using congrArg Prod.fst habk
  have hbk : b ^ (2 * k + 1) = 1 := by simpa [Prod.pow_def] using congrArg Prod.snd habk
  have ha1 : a = 1 := by
    have : a ^ (2 * k + 1) = a := by
      rw [pow_succ, pow_mul, ha2, one_pow, one_mul]
    rw [← this]; exact hak
  have hb1' : ((1 : Multiplicative (ZMod 2)), b) ∈ N := by
    have h2 : (a, b) ^ 2 ∈ N := pow_mem hab 2
    have h3 : ((1 : Multiplicative (ZMod 2)), b ^ 2) ∈ N := by
      have : (a, b) ^ 2 = ((1 : Multiplicative (ZMod 2)), b ^ 2) := by
        rw [Prod.pow_def]; simp [ha2]
      rwa [this] at h2
    have h4 := pow_mem h3 (k + 1)
    have : ((1 : Multiplicative (ZMod 2)), b ^ 2) ^ (k + 1) = (1, b) := by
      rw [Prod.pow_def]
      simp only [one_pow, Prod.mk.injEq, true_and]
      calc (b ^ 2) ^ (k + 1) = b ^ (2 * k + 1) * b := by rw [← pow_mul, ← pow_succ]; ring_nf
        _ = b := by rw [hbk, one_mul]
    rwa [this] at h4
  have hNn : N.Normal := fusionOddCore_normal _
  set M : Subgroup A := N.comap (MonoidHom.inr (Multiplicative (ZMod 2)) A)
  have hMn : M.Normal := hNn.comap _
  have hModd : Odd (Nat.card M) := by
    have hle : M.map (MonoidHom.inr (Multiplicative (ZMod 2)) A) ≤ N := by
      rintro _ ⟨m, hm, rfl⟩
      exact hm
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (fun x y h => by
      simpa using congrArg Prod.snd h)] at h1
    exact Odd.of_dvd_nat hodd h1
  have hbM : b ∈ M := hb1'
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with h | h
  · rw [h, mem_bot] at hbM
    rw [mem_bot, ha1, hbM]
    rfl
  · rw [h, Subgroup.card_top] at hModd
    exact absurd hA (Nat.not_even_iff_odd.2 hModd)

end OddCore

section Prod

variable {G : Type} [Group G]

@[expose] noncomputable def internalProdEquiv {A B : Subgroup G}
    (hAB : B ≤ centralizer (A : Set G)) (hd : Disjoint A B) : A × B ≃* (A ⊔ B : Subgroup G) :=
  have hcomm : ∀ (a : A) (b : B), Commute (A.subtype a) (B.subtype b) := fun a b =>
    mem_centralizer_iff.1 (hAB b.2) a a.2
  have hinj : Function.Injective (A.subtype.noncommCoprod B.subtype hcomm) := by
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨A.subtype_injective, B.subtype_injective, by simpa only [range_subtype] using hd⟩
  (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [MonoidHom.noncommCoprod_range, range_subtype, range_subtype]))

end Prod

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F L1 N : Subgroup G}

namespace Setup

variable (S : Setup L z t F L1 N)

include S

theorem inf_centralizer_eq : normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) =
    zpowers z ⊔ (normalizer (F : Set G) ⊓ L) := by
  rw [normalizer_inf_centralizer_z_eq S.one S.nd S.L1_normE S.L1_cz S.F_le,
    N_inf_centralizer_eq S.one S.fused S.nd, sup_comm]

theorem Q_le_X : zpowers z ⊔ (normalizer (F : Set G) ⊓ L) ≤ normalizer (L1 : Set G) := by
  rw [← S.inf_centralizer_eq]
  exact inf_le_left

noncomputable def PiQ : ↥(zpowers z ⊔ (normalizer (F : Set G) ⊓ L)) →* Xbar L1 :=
  (QuotientGroup.mk' _).comp (Subgroup.inclusion S.Q_le_X)

theorem range_PiQ : S.PiQ.range = centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} :
    Set (Xbar L1)) := by
  rw [S.centralizer_zbar_eq]
  ext q
  constructor
  · rintro ⟨⟨a, ha⟩, rfl⟩
    refine ⟨⟨a, S.Q_le_X ha⟩, ?_, rfl⟩
    have : a ∈ normalizer (L1 : Set G) ⊓ centralizer ({z} : Set G) := S.inf_centralizer_eq ▸ ha
    exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 this).2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [← S.inf_centralizer_eq]
    exact Subgroup.mem_inf.2 ⟨y.2, Subgroup.mem_subgroupOf.1 hy⟩

theorem ker_PiQ : S.PiQ.ker = F.subgroupOf (zpowers z ⊔ (normalizer (F : Set G) ⊓ L)) := by
  ext ⟨q, hq⟩
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  show (QuotientGroup.mk ⟨q, S.Q_le_X hq⟩ : Xbar L1) = 1 ↔ q ∈ F
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  constructor
  · intro hqC
    have h1 := centralizer_X_z_inf_C S.one S.nd S.L1_normE S.L1_cz S.F_le S.L1_comm S.L1_card
      S.K_eq S.z_norm
    rw [← h1]
    exact Subgroup.mem_inf.2 ⟨S.inf_centralizer_eq ▸ hq, hqC⟩
  · intro hqF
    exact mem_centralizer_iff.2 fun x hx => S.L1_comm x hx q (S.F_le hqF)

theorem centralizer_zbar_equiv (hA7 : NormQuotA7 (normalizer (F : Set G) ⊓ L) F) :
    Nonempty (centralizer ({(QuotientGroup.mk S.zX : Xbar L1)} : Set (Xbar L1)) ≃*
      Multiplicative (ZMod 2) × alternatingGroup (Fin 7)) := by
  classical
  set D : Subgroup G := normalizer (F : Set G) ⊓ L with hD
  obtain ⟨ψ₀, hψ₀, hker₀⟩ := hA7
  have hDL : D ≤ L := inf_le_right
  have hz2 : z * z = 1 := S.one.z_mul_self
  have hDc : D ≤ centralizer (zpowers z : Set G) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact (Commute.zpow_left (show Commute z d from S.one.z_comm d (hDL hd)) k).eq
  have hdisj : Disjoint (zpowers z) D := (disjoint_zpowers S.one hDL).symm
  let e := internalProdEquiv hDc hdisj
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) S.one.z_ne_one
  have hcard2 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hzo]
  have : IsCyclic (zpowers z) := isCyclic_of_prime_card hcard2
  have hcardM : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp
  have : IsCyclic (Multiplicative (ZMod 2)) := isCyclic_of_prime_card hcardM
  let e₁ : zpowers z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by rw [hcard2, hcardM])
  let θ : ↥(zpowers z ⊔ D) →* Multiplicative (ZMod 2) × alternatingGroup (Fin 7) :=
    (e₁.toMonoidHom.prodMap ψ₀).comp e.symm.toMonoidHom
  have hθsurj : Function.Surjective θ :=
    (e₁.surjective.prodMap hψ₀).comp e.symm.surjective
  have hθker : θ.ker = F.subgroupOf (zpowers z ⊔ D) := by
    ext q
    obtain ⟨⟨c, d⟩, rfl⟩ := e.surjective q
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show (e₁ (e.symm (e (c, d))).1, ψ₀ (e.symm (e (c, d))).2) = 1 ↔ _
    rw [MulEquiv.symm_apply_apply, Prod.mk_eq_one, map_eq_one_iff _ e₁.injective]
    show c = 1 ∧ ψ₀ d = 1 ↔ (c : G) * d ∈ F
    constructor
    · rintro ⟨hc, hd⟩
      have hd' : (d : G) ∈ F := by
        have : d ∈ ψ₀.ker := hd
        rw [hker₀] at this
        exact this
      rw [hc]
      simpa using hd'
    · intro h
      have hcL : (c : G) ∈ L := by
        have : (c : G) = (c * d) * (d : G)⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ (S.nd.F_le h) (Subgroup.inv_mem _ (hDL d.2))
      have hc1 : (c : G) = 1 :=
        Subgroup.disjoint_def.1 (disjoint_zpowers S.one le_rfl) hcL c.2
      have hc : c = 1 := Subtype.ext hc1
      refine ⟨hc, ?_⟩
      have hdF : (d : G) ∈ F := by
        rw [hc1, one_mul] at h
        exact h
      have : d ∈ ψ₀.ker := by
        rw [hker₀]
        exact hdF
      exact this
  have hker : S.PiQ.ker = θ.ker := by rw [S.ker_PiQ, hθker]
  exact ⟨(MulEquiv.subgroupCongr S.range_PiQ.symm).trans
    ((QuotientGroup.quotientKerEquivRange S.PiQ).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective θ hθsurj)))⟩

end Setup

end CFSG.EvenSporadicStandard.M23Std
