module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Local.FittingSplitsNormalHall
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.FrattiniArgumentNormalSylow
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.SigmaCoreNontrivial
import CFSG.FeitThompson.Local.CentralizerSemidirectCyclicTauTwoSupport
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Local.SigmaComplementExistsNontrivial
import CFSG.FeitThompson.Local.SigmaComplementAbelianNilpotent
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup
open scoped Pointwise

universe u

variable {G : Type*} [Group G]

theorem sylowPiPart_congr {X : Type*} [Group X] {π π' : Set ℕ}
    (h : ∀ p : ℕ, p.Prime → (p ∈ π ↔ p ∈ π')) : sylowPiPart π X = sylowPiPart π' X :=
  le_antisymm (sylowPiPart_le fun p hp hπ P => sylow_le_sylowPiPart hp ((h p hp).1 hπ) P)
    (sylowPiPart_le fun p hp hπ P => sylow_le_sylowPiPart hp ((h p hp).2 hπ) P)

theorem eq_map_sylowPiPart_of_isSylowProduct [Finite G] {F Y : Subgroup G} {π : Set ℕ}
    (hFnil : Group.IsNilpotent ↥F) (hY : IsSylowProduct Y F π) :
    Y = (sylowPiPart π ↥F).map F.subtype := by
  have _i := hFnil
  obtain ⟨Q, hQ, rfl⟩ := hY
  refine le_antisymm (iSup₂_le fun p hp => ?_) ?_
  · obtain ⟨hQle, hQcard⟩ := hQ p hp.1 hp.2
    by_cases hp' : p.Prime
    · have _i : Fact p.Prime := ⟨hp'⟩
      have hcard : Nat.card ↥((Q p).subgroupOf F) = p ^ (Nat.card ↥F).factorization p := by
        rw [natCard_subgroupOf_of_le hQle]; exact hQcard
      have h1 : ((Q p).subgroupOf F) ≤ sylowPiPart π ↥F := by
        have := sylow_le_sylowPiPart (X := ↥F) hp' hp.1 (Sylow.ofCard _ hcard)
        rwa [Sylow.coe_ofCard] at this
      calc Q p = ((Q p).subgroupOf F).map F.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hQle).symm
        _ ≤ _ := Subgroup.map_mono h1
    · have h1 : Nat.card ↥(Q p) = 1 := by
        rw [hQcard, Nat.factorization_eq_zero_of_not_prime _ hp', pow_zero]
      rw [Subgroup.card_eq_one.1 h1]
      exact bot_le
  · rw [Subgroup.map_le_iff_le_comap]
    refine sylowPiPart_le fun p hp hπ P => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have _i : Fact p.Prime := ⟨hp⟩
    by_cases hd : p ∣ Nat.card ↥F
    · obtain ⟨hQle, hQcard⟩ := hQ p hπ hd
      have hcard : Nat.card ↥((Q p).subgroupOf F) = p ^ (Nat.card ↥F).factorization p := by
        rw [natCard_subgroupOf_of_le hQle]; exact hQcard
      have _i := subsingleton_sylow_of_isNilpotent p ↥F
      have heq : (P : Subgroup ↥F) = (Q p).subgroupOf F := by
        rw [Subsingleton.elim P (Sylow.ofCard _ hcard), Sylow.coe_ofCard]
      rw [heq, Subgroup.map_subgroupOf_eq_of_le hQle]
      exact le_iSup₂ (f := fun (q : ℕ) (_ : q ∈ {p ∈ π | p ∣ Nat.card ↥F}) => Q q) p ⟨hπ, hd⟩
    · have h1 : Nat.card ↥(P : Subgroup ↥F) = 1 := by
        rw [P.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
      rw [Subgroup.card_eq_one.1 h1, Subgroup.map_bot]
      exact bot_le

private theorem isMulComm_of_mulEquiv {A B : Type*} [Mul A] [Mul B] [IsMulCommutative B]
    (e : A ≃* B) : IsMulCommutative A := by
  refine ⟨⟨fun a b => ?_⟩⟩
  have h : e (a * b) = e (b * a) := by
    rw [map_mul, map_mul]; exact IsMulCommutative.is_comm.comm _ _
  exact e.injective h

private theorem isNilpotent_of_isMulComm (A : Type*) [Group A] [IsMulCommutative A] :
    Group.IsNilpotent A := by
  have h : Std.Commutative (α := A) (· * ·) := IsMulCommutative.is_comm
  let _ : CommGroup A := { mul_comm := h.comm }
  infer_instance

private theorem sylow_map_mulEquiv {A B : Type*} [Group A] [Group B] {p : ℕ}
    (e : A ≃* B) (P : Sylow p A) :
    ∃ Q : Sylow p B, (Q : Subgroup B) = (P : Subgroup A).map e.toMonoidHom := by
  have hinj : Function.Injective (e.symm.toMonoidHom : B →* A) := e.symm.injective
  have hle : (P : Subgroup A) ≤ (e.symm.toMonoidHom : B →* A).range := by
    rw [MonoidHom.range_eq_top.2 (e.symm.surjective)]; exact le_top
  refine ⟨P.comapOfInjective (e.symm.toMonoidHom : B →* A) hinj hle, ?_⟩
  rw [Sylow.coe_comapOfInjective, Subgroup.map_equiv_eq_comap_symm']

private theorem sylowPiPart_map_mulEquiv_le {A B : Type*} [Group A] [Group B] (π : Set ℕ)
    (e : A ≃* B) : (sylowPiPart π A).map e.toMonoidHom ≤ sylowPiPart π B := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sylowPiPart_le fun p hp hπ P => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  obtain ⟨Q, hQ⟩ := sylow_map_mulEquiv e P
  rw [← hQ]
  exact sylow_le_sylowPiPart hp hπ Q

private theorem sylowPiPart_map_mulEquiv {A B : Type*} [Group A] [Group B] (π : Set ℕ)
    (e : A ≃* B) : (sylowPiPart π A).map e.toMonoidHom = sylowPiPart π B := by
  refine le_antisymm (sylowPiPart_map_mulEquiv_le π e) ?_
  have h := sylowPiPart_map_mulEquiv_le π e.symm
  intro x hx
  have : e.symm x ∈ sylowPiPart π A := h ⟨x, hx, rfl⟩
  exact ⟨e.symm x, this, by simp⟩

private theorem map_sylowPiPart_map_subtype {H : Subgroup G} (N : Subgroup ↥H) (π : Set ℕ) :
    (sylowPiPart π ↥(N.map H.subtype)).map (N.map H.subtype).subtype
      = ((sylowPiPart π ↥N).map N.subtype).map H.subtype := by
  set e := N.equivMapOfInjective H.subtype H.subtype_injective with he
  rw [← sylowPiPart_map_mulEquiv π e, Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem le_centralizer_comm {A B : Subgroup G} (h : A ≤ centralizer (B : Set G)) :
    B ≤ centralizer (A : Set G) := by
  rw [← commutator_eq_bot_iff_le_centralizer] at h ⊢
  rw [commutator_comm]; exact h

private theorem commutator_sup_self_eq_bot {A B : Subgroup G} (hA : ⁅A, A⁆ = ⊥) (hB : ⁅B, B⁆ = ⊥)
    (hAB : ⁅A, B⁆ = ⊥) : ⁅A ⊔ B, A ⊔ B⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer] at hA hB hAB ⊢
  have hBA : B ≤ centralizer (A : Set G) := le_centralizer_comm hAB
  refine sup_le ?_ ?_
  · intro a ha
    rw [mem_centralizer_iff]
    intro h hh
    have hsub : A ⊔ B ≤ centralizer ({a} : Set G) :=
      sup_le (le_trans hA (centralizer_le (by simpa using ha)))
        (le_trans hBA (centralizer_le (by simpa using ha)))
    exact ((mem_centralizer_iff.1 (hsub hh)) a rfl).symm
  · intro b hb
    rw [mem_centralizer_iff]
    intro h hh
    have hsub : A ⊔ B ≤ centralizer ({b} : Set G) :=
      sup_le (le_trans hAB (centralizer_le (by simpa using hb)))
        (le_trans hB (centralizer_le (by simpa using hb)))
    exact ((mem_centralizer_iff.1 (hsub hh)) b rfl).symm

private theorem nonempty_mulEquiv_quotient_of_complement {K : Type*} [Group K] {A B : Subgroup K}
    [A.Normal] (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = ⊥) : Nonempty (↥B ≃* K ⧸ A) := by
  set f : ↥B →* K ⧸ A := (QuotientGroup.mk' A).comp B.subtype with hf
  have hker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hmem : (y : K) ∈ A := by
      have : (QuotientGroup.mk' A) (y : K) = 1 := hy
      exact (QuotientGroup.eq_one_iff _).1 this
    have hmem2 : (y : K) ∈ A ⊓ B := ⟨hmem, y.2⟩
    rw [hinf] at hmem2
    rw [Subgroup.mem_bot]
    exact Subtype.ext (by simpa [Subgroup.mem_bot] using hmem2)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective x
    have hk : k ∈ A ⊔ B := by rw [hsup]; exact mem_top k
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hk
    obtain ⟨a, ha, y, hy, rfl⟩ := hk
    refine ⟨⟨y, hy⟩, ?_⟩
    change (QuotientGroup.mk' A) y = QuotientGroup.mk (a * y)
    rw [QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    have : y⁻¹ * a⁻¹ * (y⁻¹)⁻¹ ∈ A := Subgroup.Normal.conj_mem ‹A.Normal› a⁻¹ (A.inv_mem ha) y⁻¹
    simpa [mul_assoc] using this
  exact ⟨MulEquiv.ofBijective f ⟨(MonoidHom.ker_eq_bot_iff f).1 hker, hsurj⟩⟩

private theorem nonempty_mulEquiv_of_two_complements {C Z U V : Subgroup G}
    (hCab : IsMulCommutative ↥C) (hZ : Z ≤ C) (hU : U ≤ C) (hV : V ≤ C)
    (hZU : Z ⊔ U = C) (hZUinf : Z ⊓ U = ⊥) (hZV : Z ⊔ V = C) (hZVinf : Z ⊓ V = ⊥) :
    Nonempty (↥U ≃* ↥V) := by
  have := hCab
  have : (Z.subgroupOf C).Normal := normal_of_isMulCommutative _
  have h1 : Z.subgroupOf C ⊔ U.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hZ hU, hZU, subgroupOf_self]
  have h2 : Z.subgroupOf C ⊓ U.subgroupOf C = ⊥ := by
    rw [← subgroupOf_inf, hZUinf, bot_subgroupOf]
  have h3 : Z.subgroupOf C ⊔ V.subgroupOf C = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hZ hV, hZV, subgroupOf_self]
  have h4 : Z.subgroupOf C ⊓ V.subgroupOf C = ⊥ := by
    rw [← subgroupOf_inf, hZVinf, bot_subgroupOf]
  obtain ⟨e1⟩ := nonempty_mulEquiv_quotient_of_complement h1 h2
  obtain ⟨e2⟩ := nonempty_mulEquiv_quotient_of_complement h3 h4
  exact ⟨((subgroupOfEquivOfLe hU).symm.trans (e1.trans e2.symm)).trans (subgroupOfEquivOfLe hV)⟩

private theorem isMulCommutative_of_map_eq_top {A B : Type*} [Group A] [Group B] (f : A →* B)
    {T : Subgroup A} [IsMulCommutative ↥T] (h : T.map f = ⊤) : IsMulCommutative B := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : x ∈ T.map f := h ▸ mem_top x
  have hy : y ∈ T.map f := h ▸ mem_top y
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  have h2 : (⟨a, ha⟩ : ↥T) * ⟨b, hb⟩ = (⟨b, hb⟩ : ↥T) * ⟨a, ha⟩ := mul_comm' _ _
  have h3 : a * b = b * a := congrArg (Subtype.val) h2
  rw [← map_mul, ← map_mul, h3]

private theorem isMulCommutativeQuotient_of_prod {W S T : Subgroup G} (hTW : T ≤ W)
    (hnorm : W ≤ normalizer (S : Set G)) (habel : IsMulCommutative ↥T)
    (hprod : (W : Set G) = (S : Set G) * (T : Set G)) :
    IsMulCommutativeQuotient W S := by
  have hSn : (S.subgroupOf W).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  refine ⟨hSn, ?_⟩
  have := hSn
  have := habel
  have : IsMulCommutative ↥(T.subgroupOf W) := isMulComm_of_mulEquiv (subgroupOfEquivOfLe hTW)
  refine isMulCommutative_of_map_eq_top (QuotientGroup.mk' (S.subgroupOf W))
    (T := T.subgroupOf W) ?_
  rw [eq_top_iff]
  intro q _
  induction q using QuotientGroup.induction_on with
  | _ w =>
  have hw : (w : G) ∈ (S : Set G) * (T : Set G) := hprod ▸ w.2
  obtain ⟨s, hs, t, ht, hst⟩ := hw
  refine ⟨⟨t, hTW ht⟩, mem_subgroupOf.2 ht, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  change t⁻¹ * (w : G) ∈ S
  rw [← hst]
  have h2 : t⁻¹ * (s * t) = t⁻¹ * s * t := by group
  rw [h2]
  have hinvt : t⁻¹ ∈ normalizer (S : Set G) := (normalizer (S : Set G)).inv_mem (hnorm (hTW ht))
  have := (mem_normalizer_iff.1 hinvt) s
  simpa using this.1 hs

private theorem commutator_eq_map_commutator (W : Subgroup G) :
    ⁅W, W⁆ = (_root_.commutator ↥W).map W.subtype := by
  rw [_root_.commutator, Subgroup.map_commutator, map_top_subtype]

private theorem commutator_commutator_le {M S : Subgroup G} (hSder : S ≤ ⁅M, M⁆)
    (h : IsMulCommutativeQuotient (⁅M, M⁆ : Subgroup G) S) :
    ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ S := by
  obtain ⟨hn, hab⟩ := h
  have := hn
  have h2 : _root_.commutator ↥(⁅M, M⁆ : Subgroup G) ≤ S.subgroupOf (⁅M, M⁆ : Subgroup G) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.1 hab
  calc ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆
      = (_root_.commutator ↥(⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype :=
        commutator_eq_map_commutator _
    _ ≤ (S.subgroupOf (⁅M, M⁆ : Subgroup G)).map (⁅M, M⁆ : Subgroup G).subtype :=
        Subgroup.map_mono h2
    _ = S := map_subgroupOf_eq_of_le hSder

private theorem normal_inf_centralizer_subgroupOf {H S : Subgroup G}
    (hHS : H ≤ normalizer (S : Set G)) :
    ((H ⊓ centralizer (S : Set G)).subgroupOf H).Normal := by
  constructor
  intro n hn g
  rw [mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
  obtain ⟨-, hn2⟩ := hn
  refine ⟨H.mul_mem (H.mul_mem g.2 n.2) (H.inv_mem g.2), ?_⟩
  rw [mem_centralizer_iff]
  intro s hs
  have hconj : (g : G)⁻¹ * s * (g : G) ∈ S := by
    have := (mem_normalizer_iff.1 (hHS (H.inv_mem g.2))) s
    simpa using this.1 hs
  have hc := (mem_centralizer_iff.1 hn2) _ hconj
  have key : (g : G) * ((g : G)⁻¹ * s * (g:G)) * (n:G) * (g:G)⁻¹
       = (g:G) * (n:G) * ((g:G)⁻¹ * s * (g:G)) * (g:G)⁻¹ := by
    rw [mul_assoc ((g:G)), mul_assoc ((g:G)), hc]
    group
  have hcoe : ((g * n * g⁻¹ : ↥H) : G) = (g:G) * (n:G) * (g:G)⁻¹ := by push_cast; rfl
  rw [hcoe]
  calc s * ((g:G) * (n:G) * (g:G)⁻¹)
      = (g : G) * ((g : G)⁻¹ * s * (g:G)) * (n:G) * (g:G)⁻¹ := by group
    _ = (g:G) * (n:G) * ((g:G)⁻¹ * s * (g:G)) * (g:G)⁻¹ := key
    _ = ((g:G) * (n:G) * (g:G)⁻¹) * s := by group

private theorem centralizer_structure [Finite G] {M Y X : Subgroup G}
    (hdir : IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y)
    (hXle : X ≤ M ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) (hXcyc : IsCyclic ↥X)
    (hXpi : IsPiSubgroup (tauTwoPrimes M) X)
    (hXsd : FreeCore.IsInternalSemidirectProduct
      (M ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G))
      (sigmaCore M ⊓ centralizer ((sigmaCore M : Subgroup G) : Set G)) X) :
    IsCyclic ↥Y ∧ ((Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tauTwoPrimes M ∧
      ((mixedFitting M : Set G) = (sigmaCore M : Set G) *
        ((centralizerWithin M (sigmaCore M) : Subgroup G) : Set G)) := by
  set S := sigmaCore M with hS
  set C := M ⊓ centralizer (S : Set G) with hC
  set Z := S ⊓ centralizer (S : Set G) with hZ
  have hSM : S ≤ M := sigmaCore_le M
  have hSF : S ≤ mixedFitting M := hdir.left_le
  have hYF : Y ≤ mixedFitting M := hdir.right_le
  have hZC : Z ≤ C := inf_le_inf_right _ hSM
  have hCM : C ≤ M := inf_le_left
  have hYcentS : Y ≤ centralizer (S : Set G) :=
    le_centralizer_comm (commutator_eq_bot_iff_le_centralizer.1 hdir.commutator_eq_bot)
  have hYM : Y ≤ M := le_trans hYF (mixedFitting_le M)
  have hYC : Y ≤ C := le_inf hYM hYcentS
  have hZab : ⁅Z, Z⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    exact le_trans inf_le_right (centralizer_le inf_le_left)
  have hXab : ⁅X, X⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    have := hXcyc
    intro x hx
    rw [mem_centralizer_iff]
    intro y hy
    have : (⟨y, hy⟩ : ↥X) * ⟨x, hx⟩ = (⟨x, hx⟩ : ↥X) * ⟨y, hy⟩ := mul_comm' _ _
    simpa using congrArg Subtype.val this
  have hZX : ⁅Z, X⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    refine le_centralizer_comm ?_
    exact le_trans hXle (le_trans inf_le_right (centralizer_le inf_le_left))
  have hCsup : Z ⊔ X = C := hXsd.sup_eq
  have hCab : IsMulCommutative ↥C := by
    have hcomm : ⁅C, C⁆ = ⊥ := by
      rw [← hCsup]; exact commutator_sup_self_eq_bot hZab hXab hZX
    rw [commutator_eq_bot_iff_le_centralizer] at hcomm
    refine ⟨⟨fun a b => ?_⟩⟩
    have := (mem_centralizer_iff.1 (hcomm a.2)) (b : G) b.2
    exact Subtype.ext (by simpa using this.symm)
  have hnormC : (C.subgroupOf M).Normal :=
    normal_inf_centralizer_subgroupOf (le_normalizer_sigmaCore M)
  have hnilC : Group.IsNilpotent ↥(C.subgroupOf M) := by
    have := hCab
    have : IsMulCommutative ↥(C.subgroupOf M) := isMulComm_of_mulEquiv (subgroupOfEquivOfLe hCM)
    exact isNilpotent_of_isMulComm _
  have hCF : C ≤ mixedFitting M := by
    have h1 := le_fittingRaw_of_normal_of_isNilpotent hnormC hnilC
    have h2 := Subgroup.map_mono (f := M.subtype) h1
    rw [map_subgroupOf_eq_of_le hCM] at h2
    rwa [mixedFitting_eq]
  have hprod : (mixedFitting M : Set G) = (S : Set G) * (C : Set G) := by
    refine le_antisymm ?_ ?_
    · rw [hdir.coe_eq_mul]
      exact Set.mul_subset_mul_left (fun y hy => hYC hy)
    · intro x hx
      obtain ⟨s, hs, c, hc, rfl⟩ := hx
      exact (mixedFitting M).mul_mem (hSF hs) (hCF hc)
  have hZYsup : Z ⊔ Y = C := by
    refine le_antisymm (sup_le hZC hYC) ?_
    intro c hc
    have hcF : (c : G) ∈ (S : Set G) * (Y : Set G) := hdir.coe_eq_mul ▸ hCF hc
    obtain ⟨s, hs, y, hy, rfl⟩ := hcF
    have hyc : y ∈ centralizer (S : Set G) := hYcentS hy
    have hsc : s ∈ centralizer (S : Set G) := by
      have heq : s = (s * y) * y⁻¹ := by group
      rw [heq]
      exact (centralizer (S : Set G)).mul_mem hc.2 ((centralizer (S : Set G)).inv_mem hyc)
    exact (Subgroup.mul_mem _ (le_sup_left (a := Z) ⟨hs, hsc⟩) (le_sup_right (b := Y) hy))
  have hZYinf : Z ⊓ Y = ⊥ := by
    refine le_antisymm ?_ bot_le
    rw [← hdir.inf_eq_bot]
    exact inf_le_inf_right _ inf_le_left
  have hZXinf : Z ⊓ X = ⊥ := disjoint_iff.1 hXsd.disjoint
  obtain ⟨e⟩ := nonempty_mulEquiv_of_two_complements hCab hZC hYC hXle hZYsup hZYinf hCsup hZXinf
  have hcard : Nat.card ↥Y = Nat.card ↥X := Nat.card_congr e.toEquiv
  refine ⟨(MulEquiv.isCyclic e).2 hXcyc, ?_, ?_⟩
  · intro p hp
    rw [hcard] at hp
    exact isPiSubgroup_iff.1 hXpi p (by simpa using hp)
  · rw [hprod, centralizerWithin]

theorem fittingStructure_of_isNilpotent_sigmaCore
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u})
    {G : Type u} [Group G] [Finite G] (hG : IsFBGAmbient G)
    {M : Subgroup G} (hM : IsCoatom M) (hnil : Group.IsNilpotent ↥(sigmaCore M))
    {Y : Subgroup G}
    (hY : IsSylowProduct Y (mixedFitting M) {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M}) :
    IsCyclic ↥Y ∧
      ((Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tauTwoPrimes M ∧
      IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y ∧
      ((mixedFitting M : Set G) = (sigmaCore M : Set G) *
        ((centralizerWithin M (sigmaCore M) : Subgroup G) : Set G)) ∧
      IsMulCommutativeQuotient (⁅M, M⁆ : Subgroup G) (hallCoreIn M) ∧
      ⁅(⁅M, M⁆ : Subgroup G), (⁅M, M⁆ : Subgroup G)⁆ ≤ sigmaCore M := by
  have _i : Fintype G := Fintype.ofFinite G
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hGmin2 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have _i2 : Nontrivial G := hG.isSimpleGroup.toNontrivial
  obtain ⟨hHallOf, hHallG, hSder⟩ := h₁ G hGmin M hM
  have hHeq : hallCoreIn M = sigmaCore M :=
    (FBG_normal_hall_core_sigma_containment.{u} G hG M hM).2.2 hnil
  have hYeq : Y = (fittingPiPart (sigmaPrimes M)ᶜ ↥M).map M.subtype := by
    have hq1 := eq_map_sylowPiPart_of_isSylowProduct (isNilpotent_mixedFitting M) hY
    have hq2 : sylowPiPart {p : ℕ | p.Prime ∧ p ∉ sigmaPrimes M} ↥(mixedFitting M)
        = sylowPiPart (sigmaPrimes M)ᶜ ↥(mixedFitting M) :=
      sylowPiPart_congr (fun p hp => ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩)
    rw [hq1, hq2, fittingPiPart_eq_map, mixedFitting_eq, map_sylowPiPart_map_subtype]
  have hdir : IsInternalDirectProduct (mixedFitting M) (sigmaCore M) Y := by
    rw [hYeq, mixedFitting_eq]
    have hNnormal : ((sigmaCore M).subgroupOf M).Normal := sigmaCore_normal_subgroupOf M
    have : Group.IsNilpotent ↥((sigmaCore M).subgroupOf M) :=
      Group.nilpotent_of_mulEquiv (subgroupOfEquivOfLe (sigmaCore_le M)).symm
    have hdp := isInternalDirectProduct_map_fittingRaw hNnormal hHallOf.2
    rw [fittingRaw_eq_top_of_isNilpotent ↥((sigmaCore M).subgroupOf M), map_top_subtype] at hdp
    have h3 := isInternalDirectProduct_map (M.subtype_injective) hdp
    rwa [map_subgroupOf_eq_of_le (sigmaCore_le M)] at h3
  have hSne : sigmaCore M ≠ ⊥ := (FBG_sigma_core_nontrivial h₁ G hGmin M hM).2
  have hHallSS : IsHallPiSubgroupOf (sigmaPrimes M) (sigmaCore M) (sigmaCore M) := by
    refine ⟨le_refl _, ?_, ?_⟩
    · rw [subgroupOf_self]
      refine isPiSubgroup_iff.2 fun p hp => ?_
      exact isPiSubgroup_iff.1 hHallG.isPiSubgroup p (by simpa using hp)
    · rw [subgroupOf_self]; simp
  obtain ⟨X, hXle, hXcyc, hXpi, hXsd⟩ :=
    FBG_sigma_hall_centralizer_cyclic_complement h₁ h₂ h₃ h₄ h₆ h₇
      G hGmin M hM (sigmaPrimes M) (sigmaCore M) hSne hHallSS
  obtain ⟨hcyc, hτ, hprod⟩ := centralizer_structure hdir hXle hXcyc hXpi hXsd
  obtain ⟨E, hEM, hEne, hEsd⟩ :=
    exists_sigmaComplement hG.not_isMulCommutative hM (hG.isSolvable M hM.1) hHallOf hSder
  have hSC : _root_.CFSG.FeitThompson.IsSigmaComplement M E := ⟨hM, hEsd⟩
  obtain ⟨-, -, hMder, -, -, -, -, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FNI_sigma_complement_prime_data h₁ G hGmin2 M E hSC
  have hEab : IsMulCommutative ↥(⁅E, E⁆ : Subgroup G) :=
    (FBG_sigma_complement_abelian_nilpotent h₁ h₅ G hGmin M hM).2 E hEsd
  have hEEM : (⁅E, E⁆ : Subgroup G) ≤ (⁅M, M⁆ : Subgroup G) := commutator_mono hEM hEM
  have hnormS : (⁅M, M⁆ : Subgroup G) ≤ normalizer ((sigmaCore M : Subgroup G) : Set G) :=
    le_trans (commutator_le_self M) (le_normalizer_sigmaCore M)
  have hq := isMulCommutativeQuotient_of_prod hEEM hnormS hEab hMder
  exact ⟨hcyc, hτ, hdir, hprod, by rw [hHeq]; exact hq, commutator_commutator_le hSder hq⟩

theorem FBG_nilpotent_sigma_core_fitting_structure
    (h₁ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : Statements.FBG_tau_two_hall_abelian.{u})
    (h₃ : Statements.FNI_kappa_normalizer_centralizer_structure.{u})
    (h₄ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : Statements.FNI_outside_sigma_plane_sylow.{u})
    (h₆ : Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : Statements.FTS_tau_one_fixed_line_centralizer_unique.{u}) :
    Statements.FBG_nilpotent_sigma_core_fitting_structure.{u} := by
  intro G _ _ hG M hM hnil Y hY
  have _i : Fintype G := Fintype.ofFinite G
  have hGmin : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hHeq : hallCoreIn M = sigmaCore M :=
    (FBG_normal_hall_core_sigma_containment.{u} G hG M hM).2.2 hnil
  obtain ⟨hcyc, hτ, hdir, hprod, hquot, hM''⟩ :=
    fittingStructure_of_isNilpotent_sigmaCore h₁ h₂ h₃ h₄ h₅ h₆ h₇ hG hM hnil hY
  have hle : hallCoreIn M ≤ (⁅M, M⁆ : Subgroup G) := by
    rw [hHeq]; exact (h₁ G hGmin M hM).2.2
  exact ⟨hHeq, (FBG_sigma_core_nontrivial h₁ G hGmin M hM).2, hcyc, hτ, hdir, hprod, hle, hquot,
    hM''⟩

end

end CFSG.FeitThompson.Proofs
