module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2GenDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2Cyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Lemmas
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.InvariantTwoConstrained
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialFamilies
public import CFSG.LocalAnalysis.ABGTheoremB.Basic
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor (PointConfig pointConfig_of_u3)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial (SignalizerTrivialOn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

@[expose] def TypeSigTrivOn (Typ : ℕ → ∀ (Q : Type) [Group Q], Prop) (p : ℕ) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], Typ p K → Subgroup.center K = ⊥ → SignalizerTrivialOn p K

theorem typeSigTrivOn_u3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    TypeSigTrivOn (fun p K _ => CFSG.LocalAnalysis.RankThreeTheoremC.IsU3Pred p K) p :=
  fun K _ _ hK _ =>
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial.signalizerTrivialU3_holds
      p hp hp5 K hK

theorem typeSigTrivOn_of_X {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} {p : ℕ} (hp : p.Prime)
    (hiso : ∀ (A B : Type) [Group A] [Group B], A ≃* B → Typ p A → Typ p B)
    (hX : ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X),
      K.Normal ∧ Subgroup.centralizer (K : Set X) = ⊥ ∧ Typ p ↥K →
      ∀ R : Sylow p X, ∀ W : Subgroup X, Nat.Coprime p (Nat.card W) →
        ((R : Subgroup X) ⊓ K) ≤ Subgroup.normalizer (W : Set X) → W = ⊥) :
    TypeSigTrivOn Typ p := by
  intro K _ _ hK hZ P W hW hnorm
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (MulAut K) :=
    Finite.of_injective (fun f : MulAut K => (f : K → K)) DFunLike.coe_injective
  let c : K →* MulAut K := MulAut.conj
  have hcinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro k hk
    have hkc : k ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 := congrArg (fun φ : MulAut K => φ y) hk
      simp only [c, MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * k = (k * y * k⁻¹) * k := by rw [h1]
        _ = k * y := by group
    rw [hZ, Subgroup.mem_bot] at hkc
    exact hkc
  let Kin : Subgroup (MulAut K) := c.range
  have hKinN : Kin.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := hn
    refine ⟨g k, ?_⟩
    ext y
    simp [c, MulAut.conj_apply]
  have hKinC : Subgroup.centralizer (Kin : Set (MulAut K)) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rw [Subgroup.mem_centralizer_iff] at hφ
    rw [Subgroup.mem_bot]
    ext k
    have hcen : (φ k)⁻¹ * k ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro z
      obtain ⟨y, rfl⟩ := φ.surjective z
      have h1 := congrArg (fun ψ : MulAut K => ψ y) (hφ (MulAut.conj k) ⟨k, rfl⟩)
      simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv] at h1
      calc φ y * ((φ k)⁻¹ * k) = (φ k)⁻¹ * ((φ k * φ y * (φ k)⁻¹) * k) := by group
        _ = (φ k)⁻¹ * ((k * φ y * k⁻¹) * k) := by rw [← h1]
        _ = (φ k)⁻¹ * k * φ y := by group
    rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcen
    simpa using hcen
  have hTypKin : Typ p ↥Kin := hiso K ↥Kin (MonoidHom.ofInjective hcinj) hK
  obtain ⟨R, hR⟩ := (P.isPGroup'.map c).exists_le_sylow
  have hRK : (R : Subgroup (MulAut K)) ⊓ Kin ≤ Subgroup.normalizer (W : Set (MulAut K)) := by
    rintro _ ⟨hxR, ⟨k, rfl⟩⟩
    have hkP : k ∈ (P : Subgroup K) := by
      have hH : IsPGroup p (((R : Subgroup (MulAut K)) ⊓ Kin).comap c) :=
        (R.isPGroup'.to_inf_left).comap_of_injective c hcinj
      have hPH : (P : Subgroup K) ≤ ((R : Subgroup (MulAut K)) ⊓ Kin).comap c :=
        fun g hg => ⟨hR (Subgroup.mem_map_of_mem c hg), ⟨g, rfl⟩⟩
      have h3 := P.3 hH hPH
      have h4 : k ∈ ((R : Subgroup (MulAut K)) ⊓ Kin).comap c := ⟨hxR, ⟨k, rfl⟩⟩
      rwa [h3] at h4
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · exact fun hw => hnorm k hkP w hw
    · intro h
      have h1 := hnorm k⁻¹ ((P : Subgroup K).inv_mem hkP) _ h
      have e : (MulAut.conj k⁻¹ : MulAut K) * (c k * w * (c k)⁻¹) * (MulAut.conj k⁻¹)⁻¹ = w := by
        have hc1 : (MulAut.conj k⁻¹ : MulAut K) = (c k)⁻¹ := by simp [c]
        rw [hc1]
        group
      rwa [e] at h1
  exact hX (MulAut K) Kin ⟨hKinN, hKinC, hTypKin⟩ R W hW hRK

private theorem c47_burnside_normalizer_le_centralizer {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (Q : Sylow p Y) (hQc : IsCyclic (Q : Subgroup Y)) {x : Y}
    (hxQ : x ∈ (Q : Subgroup Y)) (hxo : orderOf x = p) (hxc : ∀ y : Y, y * x = x * y) :
    Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤ Subgroup.centralizer ((Q : Subgroup Y) : Set Y) := by
  haveI := hQc
  haveI : Fact p.Prime := ⟨hp⟩
  intro g hg
  set Qs : Subgroup Y := (Q : Subgroup Y) with hQs
  set φ : Subgroup.normalizer (Qs : Set Y) →* MulAut Qs := Qs.normalizerMonoidHom with hφ
  set s : ℕ := φ.ker.index with hs
  have hQN : Qs ≤ Subgroup.normalizer (Qs : Set Y) := Subgroup.le_normalizer
  have hle : Qs.subgroupOf (Subgroup.normalizer (Qs : Set Y)) ≤ φ.ker := by
    intro n hn
    rw [hφ, Subgroup.normalizerMonoidHom_ker]
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact Subgroup.le_centralizer Qs hn
  have hcop : Nat.Coprime p s := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    apply Q.not_dvd_index
    refine hdvd.trans ?_
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    exact Subgroup.relIndex_dvd_index_of_le hQN
  have hgD : ∀ d ∈ Qs, g * d * g⁻¹ ∈ Qs := fun d hd => ((Subgroup.mem_normalizer_iff.mp hg) d).mp hd
  have hgx : g * x * g⁻¹ = x := by rw [hxc g, mul_assoc, mul_inv_cancel, mul_one]
  have hDp : ∀ d ∈ Qs, ∃ k : ℕ, d ^ (p ^ k) = 1 := by
    intro d hd
    obtain ⟨k, hk⟩ := Q.isPGroup' ⟨d, hd⟩
    exact ⟨k, congrArg Subtype.val hk⟩
  have hgs : ∀ d ∈ Qs, (g ^ s) * d * (g ^ s)⁻¹ = d := by
    intro d hd
    have h1 : (⟨g, hg⟩ : Subgroup.normalizer (Qs : Set Y)) ^ s ∈ φ.ker := Subgroup.pow_index_mem _ _
    rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    have h2 := h1 d hd
    simp only [Subgroup.coe_pow] at h2
    rw [mul_inv_eq_iff_eq_mul]
    exact h2.symm
  have key := cyclic_coprime_aut_trivial hp (D := Qs) hDp hxQ hxo hgD hgx hcop hgs
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have := key d hd
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

private theorem c47_burnside_exists_complement {Y : Type*} [Group Y] [Finite Y] {p : ℕ}
    (hp : p.Prime) (Q : Sylow p Y)
    (hQ : Subgroup.normalizer ((Q : Subgroup Y) : Set Y) ≤
      Subgroup.centralizer ((Q : Subgroup Y) : Set Y)) :
    ∃ N : Subgroup Y, (∀ n ∈ N, Nat.Coprime p (orderOf n)) ∧
      (∀ y : Y, Nat.Coprime p (orderOf y) → y ∈ N) ∧
      (∀ y : Y, ∃ n ∈ N, ∃ d ∈ (Q : Subgroup Y), y = n * d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨(MonoidHom.transferSylow Q hQ).ker, ?_, ?_, ?_⟩
  · intro n hn
    have h1 : orderOf n ∣ Nat.card (MonoidHom.transferSylow Q hQ).ker := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : (MonoidHom.transferSylow Q hQ).ker)
      simpa using this
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (MonoidHom.not_dvd_card_ker_transferSylow Q hQ)).coprime_dvd_right h1
  · intro y hy
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := Q.isPGroup' (MonoidHom.transferSylow Q hQ y)
    have h2 : orderOf (MonoidHom.transferSylow Q hQ y) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
    have h3 : orderOf (MonoidHom.transferSylow Q hQ y) ∣ orderOf y := orderOf_map_dvd _ y
    have h4 : Nat.Coprime (p ^ k) (orderOf y) := Nat.Coprime.pow_left k hy
    have h5 : orderOf (MonoidHom.transferSylow Q hQ y) = 1 := Nat.eq_one_of_dvd_coprimes h4 h2 h3
    exact orderOf_eq_one_iff.mp h5
  · intro y
    have hcomp := MonoidHom.ker_transferSylow_isComplement' Q hQ
    obtain ⟨⟨a, d⟩, h, -⟩ := hcomp.existsUnique y
    exact ⟨a.1, a.2, d.1, d.2, h.symm⟩

private theorem c47_mem_sup_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {s : G} (hs : s ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, s = a * b := by
  have hr := MonoidHom.noncommCoprod_range A.subtype B.subtype (fun a b => h a a.2 b b.2)
  rw [Subgroup.range_subtype, Subgroup.range_subtype] at hr
  rw [← hr] at hs
  obtain ⟨⟨a, b⟩, rfl⟩ := hs
  exact ⟨a, a.2, b, b.2, rfl⟩

private theorem c47_D_cyclic {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hSd : TypeSDecomp p P x J)
    (hc : PointConfig Typ G p P M x J) : IsCyclic ↥(u3S P x ⊓ u3K0 p x J) := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Z, hZc, -, hZS, hZT, -, hTZS⟩ := hSd
  haveI := hZc
  have hTconj : ∀ a ∈ u3S P x, ∀ t ∈ u3T P x J, a * t * a⁻¹ ∈ u3T P x J := by
    intro a ha t ht
    have ha' : a ∈ (P : Subgroup G) ∧ a ∈ Subgroup.centralizer ({x} : Set G) := ha
    have ht' : (t ∈ (P : Subgroup G) ∧ t ∈ Subgroup.centralizer ({x} : Set G)) ∧ t ∈ J := ht
    have h1 : a * t * a⁻¹ ∈ (P : Subgroup G) := mul_mem (mul_mem ha'.1 ht'.1.1) (inv_mem ha'.1)
    have h2 : a * t * a⁻¹ ∈ Subgroup.centralizer ({x} : Set G) :=
      mul_mem (mul_mem ha'.2 ht'.1.2) (inv_mem ha'.2)
    have h3 : a * t * a⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hc.cent_le ha'.2) t).mp ht'.2
    exact ⟨⟨h1, h2⟩, h3⟩
  have hTS : u3T P x J ≤ u3S P x := inf_le_left
  have hDS : u3S P x ⊓ u3K0 p x J ≤ u3S P x := inf_le_left
  have hinf : u3T P x J ⊓ (u3S P x ⊓ u3K0 p x J) = ⊥ := by
    rw [eq_bot_iff, ← u3_T_inf_K0_gen hc]
    exact inf_le_inf_left _ inf_le_right
  let T₀ : Subgroup (u3S P x) := (u3T P x J).subgroupOf (u3S P x)
  haveI hT₀n : T₀.Normal := ⟨fun n hn g => hTconj g g.2 n hn⟩
  let q : u3S P x →* u3S P x ⧸ T₀ := QuotientGroup.mk' T₀
  let g : Z →* u3S P x ⧸ T₀ := q.comp (Subgroup.inclusion hZS)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
    have hs : (s : G) ∈ u3T P x J ⊔ Z := by rw [hTZS]; exact s.2
    obtain ⟨t, ht, z, hz, hsz⟩ :=
      c47_mem_sup_of_commute (fun a ha b hb => (hZT b hb a ha).symm) hs
    refine ⟨⟨z, hz⟩, ?_⟩
    have hts : (⟨t, hTS ht⟩ : u3S P x) ∈ T₀ := ht
    have hsz' : s = ⟨t, hTS ht⟩ * ⟨z, hZS hz⟩ := Subtype.ext hsz
    show (QuotientGroup.mk (⟨z, hZS hz⟩ : u3S P x) : u3S P x ⧸ T₀) = QuotientGroup.mk s
    rw [hsz', QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (N := T₀) _).mpr hts, one_mul]
  haveI : IsCyclic (u3S P x ⧸ T₀) := isCyclic_of_surjective g hg
  let f : ↥(u3S P x ⊓ u3K0 p x J) →* u3S P x ⧸ T₀ := q.comp (Subgroup.inclusion hDS)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hd' : (QuotientGroup.mk (Subgroup.inclusion hDS d) : u3S P x ⧸ T₀) = 1 := hd
    have hdT0 : Subgroup.inclusion hDS d ∈ T₀ := (QuotientGroup.eq_one_iff (N := T₀) _).mp hd'
    have hdT : (d : G) ∈ u3T P x J := hdT0
    have hmem : (d : G) ∈ u3T P x J ⊓ (u3S P x ⊓ u3K0 p x J) := ⟨hdT, d.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  exact isCyclic_of_injective f hf

theorem k0_pComplement_of_cyclic {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hDcyc : IsCyclic ↥(u3S P x ⊓ u3K0 p x J)) (hc : PointConfig Typ G p P M x J) :
    ∃ N₀ : Subgroup G, N₀ ≤ u3K0 p x J ∧
      (∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀) ∧
      (∀ n ∈ N₀, Nat.Coprime p (orderOf n)) ∧
      ∀ k ∈ u3K0 p x J, Nat.Coprime p (orderOf k) → k ∈ N₀ := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hnorm := u3K0_conj_gen hc
  have hK₀C : u3K0 p x J ≤ Subgroup.centralizer ({x} : Set G) := fun k hk => hk.1
  have hK₀N : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer ((u3K0 p x J : Subgroup G) : Set G) := by
    intro c hcC
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · exact fun hk => hnorm c hcC k hk
    · intro hk
      have := hnorm c⁻¹ ((Subgroup.centralizer ({x} : Set G)).inv_mem hcC) _ hk
      simpa [mul_assoc] using this
  have hsyl : CFSG.ABGLocalTools.IsSylowOf p (u3S P x) (Subgroup.centralizer ({x} : Set G)) :=
    hc.generic.2.2.1
  have hsyl' : CFSG.ABGLocalTools.IsSylowOf p (u3S P x ⊓ u3K0 p x J) (u3K0 p x J) :=
    hsyl.inf_of_le_normalizer hK₀C hK₀N
  obtain ⟨Q, hQ⟩ := hsyl'.exists_sylow_eq_subgroupOf
  have hQc : IsCyclic (Q : Subgroup (u3K0 p x J)) := by
    rw [hQ]
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : u3S P x ⊓ u3K0 p x J ≤ u3K0 p x J))).mpr hDcyc
  have hxK : x ∈ u3K0 p x J := x_mem_u3K0_gen hc
  have hxC : x ∈ Subgroup.centralizer ({x} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hxSC : x ∈ (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) := ⟨hc.generic.1, hxC⟩
  have hxS : x ∈ u3S P x ⊓ u3K0 p x J := ⟨hxSC, hxK⟩
  have hxQ : (⟨x, hxK⟩ : u3K0 p x J) ∈ (Q : Subgroup (u3K0 p x J)) := by
    rw [hQ, Subgroup.mem_subgroupOf]
    exact hxS
  have hxo : orderOf (⟨x, hxK⟩ : u3K0 p x J) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hc.generic.2.1.2.2.1 hc.generic.2.1.2.1
  have hxc : ∀ y : u3K0 p x J, y * ⟨x, hxK⟩ = ⟨x, hxK⟩ * y := by
    intro y
    apply Subtype.ext
    exact (y.2.1 x (Set.mem_singleton x)).symm
  have hQN := c47_burnside_normalizer_le_centralizer hp Q hQc hxQ hxo hxc
  obtain ⟨N, hN1, hN2, hN3⟩ := c47_burnside_exists_complement hp Q hQN
  refine ⟨N.map (u3K0 p x J).subtype, Subgroup.map_subtype_le N, ?_, ?_, ?_⟩
  · intro c hcC n hn
    obtain ⟨n', hn', rfl⟩ := hn
    have hmem : c * (n' : G) * c⁻¹ ∈ u3K0 p x J := hnorm c hcC n' n'.2
    have hm : (⟨c * (n' : G) * c⁻¹, hmem⟩ : u3K0 p x J) ∈ N := by
      apply hN2
      rw [Subgroup.orderOf_mk]
      have h1 : orderOf (c * (n' : G) * c⁻¹) = orderOf (n' : G) := by
        have := orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective (n' : G)
        simpa using this
      rw [h1, Subgroup.orderOf_coe]
      exact hN1 n' hn'
    exact ⟨_, hm, rfl⟩
  · rintro n ⟨n', hn', rfl⟩
    have := hN1 n' hn'
    rwa [← Subgroup.orderOf_coe] at this
  · intro k hk hkp
    have hmem : (⟨k, hk⟩ : u3K0 p x J) ∈ N := by
      apply hN2
      rw [Subgroup.orderOf_mk]
      exact hkp
    exact ⟨⟨k, hk⟩, hmem, rfl⟩

private theorem c47_conj_hom (J H : Subgroup G) (hH : H ≤ Subgroup.normalizer (J : Set G)) :
    ∃ ι : H →* MulAut J, ∀ (c : H) (j : J), ((ι c j : J) : G) = (c : G) * j * (c : G)⁻¹ := by
  let f : ∀ c : G, c ∈ Subgroup.normalizer (J : Set G) → MulAut J := fun c hc =>
    { toFun := fun j => ⟨c * j * c⁻¹, (Subgroup.mem_normalizer_iff.mp hc j).mp j.2⟩
      invFun := fun j => ⟨c⁻¹ * j * c, by
        simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hc) j).mp j.2⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  refine ⟨{ toFun := fun c => f c (hH c.2), map_one' := ?_, map_mul' := ?_ }, fun c j => rfl⟩
  · ext j; simp [f]
  · intro a b; ext j; simp [f, mul_assoc]

private theorem c47_descent {J Q H : Type} [Group J] [Group Q] [Group H] (ψ : J →* Q)
    (hψ : Function.Surjective ψ) (ι : H →* MulAut J)
    (h : ∀ c j, ψ j = 1 → ψ (ι c j) = 1) :
    ∃ θ : H →* MulAut Q, ∀ c j, θ c (ψ j) = ψ (ι c j) := by
  have key : ∀ c : H, ∃ f : Q →* Q, ∀ j, f (ψ j) = ψ (ι c j) := by
    intro c
    refine ⟨ψ.liftOfSurjective hψ ⟨ψ.comp (ι c).toMonoidHom, fun j hj => h c j hj⟩, fun j => ?_⟩
    simp
  choose F hF using key
  have hmul : ∀ c d : H, ∀ q, F (c * d) q = F c (F d q) := by
    intro c d q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF, hF, hF]
    simp
  have hone : ∀ q, F 1 q = q := by
    intro q
    obtain ⟨j, rfl⟩ := hψ q
    rw [hF]
    simp
  let θ' : ∀ c : H, MulAut Q := fun c =>
    { toFun := F c
      invFun := F c⁻¹
      left_inv := fun q => by rw [← hmul, inv_mul_cancel, hone]
      right_inv := fun q => by rw [← hmul, mul_inv_cancel, hone]
      map_mul' := (F c).map_mul }
  refine ⟨{ toFun := θ', map_one' := ?_, map_mul' := ?_ }, fun c j => hF c j⟩
  · ext q; exact hone q
  · intro a b; ext q; exact hmul a b q

private theorem c47_exists_rho {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hc : PointConfig Typ G p P M x J) {Q : Type} [Group Q] (ψ : ↥J →* Q)
    (hψ : Function.Surjective ψ) (hker : ψ.ker = (rankThreePrimeCore p J).subgroupOf J) :
    ∃ ρ : ↥(Subgroup.centralizer ({x} : Set G)) →* MulAut Q,
      ∀ (c : ↥(Subgroup.centralizer ({x} : Set G))) (j : ↥J)
        (hj : (c : G) * (j : G) * (c : G)⁻¹ ∈ J),
        ρ c (ψ j) = ψ ⟨(c : G) * (j : G) * (c : G)⁻¹, hj⟩ := by
  have hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  obtain ⟨ι, hι⟩ := c47_conj_hom J (Subgroup.centralizer ({x} : Set G)) hCN
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  have hιker : ∀ (c : ↥(Subgroup.centralizer ({x} : Set G))) (j : J), ψ j = 1 → ψ (ι c j) = 1 := by
    intro c j hj
    rw [hOker] at hj ⊢
    rw [hι]
    exact u3_core_conj (hCN c.2) hj
  obtain ⟨θ, hθ⟩ := c47_descent ψ hψ ι hιker
  refine ⟨θ, fun c j hj => ?_⟩
  rw [hθ]
  congr 1
  exact Subtype.ext (hι c j)

private theorem c47_core_le_K0 {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G)
    (hsig : TypeSigTrivOn Typ p) (hc : PointConfig Typ G p P M x J) :
    ∀ e ∈ rankThreePrimeCore p M, e ∈ Subgroup.centralizer ({x} : Set G) → e ∈ u3K0 p x J := by
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hTP : u3T P x J ≤ (P : Subgroup G) := inf_le_left.trans inf_le_left
  have hTM : u3T P x J ≤ M := hTP.trans hPM
  have hTJ : u3T P x J ≤ J := inf_le_right
  have hTC : u3T P x J ≤ Subgroup.centralizer ({x} : Set G) :=
    (inf_le_left : u3T P x J ≤ u3S P x).trans inf_le_right
  have hOcop : Nat.Coprime p (Nat.card (rankThreePrimeCore p M)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p M
  have hMnorm : M ≤ Subgroup.normalizer (rankThreePrimeCore p M : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p M
  have hCN : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (J : Set G) := hc.cent_le
  obtain ⟨Q, iQ, ψ, hψ, hker, hQ⟩ := hc.typ
  haveI : Finite Q := Finite.of_surjective ψ hψ
  have hOker : ∀ j : J, ψ j = 1 ↔ (j : G) ∈ rankThreePrimeCore p J := by
    intro j
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  obtain ⟨ρ, hρ⟩ := c47_exists_rho hc ψ hψ hker
  have hSylJ : CFSG.ABGLocalTools.IsSylowOf p (u3T P x J) J :=
    hc.generic.2.2.1.inf_of_le_normalizer hc.le_cent hc.cent_le
  obtain ⟨Tsyl, hTsyl⟩ := hSylJ.exists_sylow_eq_subgroupOf
  let Tsyl' : Sylow p Q := Tsyl.mapSurjective hψ
  have hTsyl' : (Tsyl' : Subgroup Q) = ((u3T P x J).subgroupOf J).map ψ := by
    rw [← hTsyl]; exact Sylow.coe_mapSurjective hψ Tsyl
  have hρt : ∀ (t : G) (ht : t ∈ u3T P x J),
      ρ ⟨t, hTC ht⟩ = MulAut.conj (ψ ⟨t, hTJ ht⟩) := by
    intro t ht
    ext q
    obtain ⟨j, rfl⟩ := hψ q
    have hj : t * (j : G) * t⁻¹ ∈ J := J.mul_mem (J.mul_mem (hTJ ht) j.2) (J.inv_mem (hTJ ht))
    have h1 := hρ ⟨t, hTC ht⟩ j hj
    have e1 : (⟨t * (j : G) * t⁻¹, hj⟩ : J) = ⟨t, hTJ ht⟩ * j * (⟨t, hTJ ht⟩ : J)⁻¹ :=
      Subtype.ext rfl
    rw [MulAut.conj_apply, h1, e1, map_mul, map_mul, map_inv]
  set E : Subgroup ↥(Subgroup.centralizer ({x} : Set G)) :=
    (rankThreePrimeCore p M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
      (Subgroup.centralizer ({x} : Set G)) with hE
  set F : Subgroup (MulAut Q) := E.map ρ with hF
  have hFcop : Nat.Coprime p (Nat.card F) := by
    have h1 : Nat.card F ∣ Nat.card E := Subgroup.card_map_dvd E ρ
    have h2 : Nat.card E ∣ Nat.card (rankThreePrimeCore p M) := by
      rw [hE, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : rankThreePrimeCore p M ⊓ Subgroup.centralizer ({x} : Set G) ≤
          Subgroup.centralizer ({x} : Set G))).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact hOcop.coprime_dvd_right (h1.trans h2)
  have hFnorm : ∀ g ∈ (Tsyl' : Subgroup Q), ∀ w ∈ F,
      MulAut.conj g * w * (MulAut.conj g)⁻¹ ∈ F := by
    intro g hg w hw
    rw [hTsyl'] at hg
    obtain ⟨t₀, ht₀, rfl⟩ := hg
    obtain ⟨ε, hε, rfl⟩ := hw
    have htT : (t₀ : G) ∈ u3T P x J := ht₀
    have hεO : (ε : G) ∈ rankThreePrimeCore p M := (Subgroup.mem_subgroupOf.mp hε).1
    have hεC : (ε : G) ∈ Subgroup.centralizer ({x} : Set G) := ε.2
    have hρt' := hρt (t₀ : G) htT
    rw [← hρt', ← map_inv, ← map_mul, ← map_mul]
    refine ⟨⟨(t₀ : G), hTC htT⟩ * ε * ⟨(t₀ : G), hTC htT⟩⁻¹, ?_, rfl⟩
    rw [hE, SetLike.mem_coe, Subgroup.mem_subgroupOf]
    refine ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hMnorm (hTM htT)) (ε : G)).mp hεO
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTC htT) hεC)
        (Subgroup.inv_mem _ (hTC htT))
  have hZ : Subgroup.center Q = ⊥ :=
    u3main_center_bot (CFSG.AGLEmbedding.glbPrimeCore_le p J) hc.perfect hc.lt hc.minimal ψ hψ hker
  have hF1 : F = ⊥ := hsig Q hQ hZ Tsyl' F hFcop hFnorm
  intro e heO heC
  have hmem : ρ ⟨e, heC⟩ ∈ F :=
    Subgroup.mem_map_of_mem ρ (Subgroup.mem_subgroupOf.mpr ⟨heO, heC⟩)
  rw [hF1, Subgroup.mem_bot] at hmem
  refine ⟨heC, hCN heC, fun j hj => ?_⟩
  have hjj : e * j * e⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.mp (hCN heC) j).mp hj
  have h1 := hρ ⟨e, heC⟩ ⟨j, hj⟩ hjj
  rw [hmem, MulAut.one_apply] at h1
  have h2 : ψ (⟨e * j * e⁻¹, hjj⟩ * ⟨j, hj⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, ← h1, mul_inv_cancel]
  have := (hOker _).mp h2
  simpa using this

private theorem c47_le_pPrimeCoreIn [Fact p.Prime] {N₀ : Subgroup G}
    (hN₀C : N₀ ≤ Subgroup.centralizer ({x} : Set G))
    (hnorm : ∀ c ∈ Subgroup.centralizer ({x} : Set G), ∀ n ∈ N₀, c * n * c⁻¹ ∈ N₀)
    (hcop : ∀ n ∈ N₀, Nat.Coprime p (orderOf n)) :
    N₀ ≤ CFSG.ABGTheoremB.pPrimeCoreIn p (Subgroup.centralizer ({x} : Set G)) := by
  refine le_trans ?_ (glbPrimeCore_le_pPrimeCoreIn p _)
  refine CFSG.AGLEmbedding.le_glbPrimeCore (p := p) (H := Subgroup.centralizer ({x} : Set G))
    (N := N₀) hN₀C ?_ ?_
  · intro c hcC
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact fun hn => hnorm c hcC n hn
    · intro hn
      have := hnorm c⁻¹ (inv_mem hcC) _ hn
      simpa [mul_assoc] using this
  · by_contra hnc
    have hdvd : p ∣ Nat.card N₀ := by
      by_contra h
      exact hnc ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr h)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 := hcop (g : G) g.2
    rw [Subgroup.orderOf_coe, hg] at h1
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_self p |>.mp h1)

theorem k0_coprime_mem_pPrimeCoreIn {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop}
    (hDcyc : IsCyclic ↥(u3S P x ⊓ u3K0 p x J)) (hc : PointConfig Typ G p P M x J) :
    ∀ k ∈ u3K0 p x J, Nat.Coprime p (orderOf k) →
      k ∈ CFSG.ABGTheoremB.pPrimeCoreIn p (Subgroup.centralizer ({x} : Set G)) := by
  haveI : Fact p.Prime := ⟨hc.prime⟩
  obtain ⟨N₀, hN₀K, hN₀C, hN₀cop, hN₀all⟩ := k0_pComplement_of_cyclic hDcyc hc
  have hN₀O := c47_le_pPrimeCoreIn (N₀ := N₀) (fun n hn => (hN₀K hn).1) hN₀C hN₀cop
  exact fun k hk hkp => hN₀O (hN₀all k hk hkp)

theorem u3_cor47_gen_cyc {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G) (hD1 : TheoremD1 G)
    (hsig : TypeSigTrivOn Typ p) (hDcyc : IsCyclic ↥(u3S P x ⊓ u3K0 p x J))
    (hc : PointConfig Typ G p P M x J) :
    ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥ := by
  intro X hX2 hXO hXC
  have hp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 := hc.five
  obtain ⟨N₀, hN₀K, hN₀C, hN₀cop, hN₀all⟩ := k0_pComplement_of_cyclic hDcyc hc
  have hN₀O := c47_le_pPrimeCoreIn (N₀ := N₀) (fun n hn => (hN₀K hn).1) hN₀C hN₀cop
  have hodd := odd_card_pPrimeCoreIn_of_not_le hS hD1 hc.sigma hc.core hc.generic.2.2.2.ge
    hc.generic.2.1.2.2.2.2
  have hXN : X ≤ N₀ := by
    intro g hg
    apply hN₀all g (c47_core_le_K0 hS hsig hc g (hXO hg) (hXC hg))
    obtain ⟨k, hk⟩ := hX2 ⟨g, hg⟩
    have hdvd : orderOf g ∣ 2 ^ k := by
      have := orderOf_dvd_of_pow_eq_one hk
      rwa [Subgroup.orderOf_mk] at this
    have hcop2 : Nat.Coprime p (2 ^ k) :=
      Nat.Coprime.pow_right k ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega))
    exact hcop2.coprime_dvd_right hdvd
  have hXO' : X ≤ CFSG.ABGTheoremB.pPrimeCoreIn p (Subgroup.centralizer ({x} : Set G)) :=
    hXN.trans hN₀O
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hX2
  have hdvd : Nat.card X ∣
      Nat.card (CFSG.ABGTheoremB.pPrimeCoreIn p (Subgroup.centralizer ({x} : Set G))) :=
    Subgroup.card_dvd_of_le hXO'
  have hn0 : n = 0 := by
    by_contra hn0
    exact hodd ((dvd_pow_self 2 hn0).trans (hn ▸ hdvd))
  rw [hn0, pow_zero] at hn
  exact Subgroup.eq_bot_of_card_eq _ hn

theorem u3_cor47_gen {Typ : ℕ → ∀ (Q : Type) [Group Q], Prop} (hS : Setting G) (hD1 : TheoremD1 G)
    (hsig : TypeSigTrivOn Typ p) (hSd : TypeSDecomp p P x J) (hc : PointConfig Typ G p P M x J) :
    ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥ :=
  u3_cor47_gen_cyc hS hD1 hsig (c47_D_cyclic hSd hc) hc

theorem u3_cor47 (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J) :
    ∀ X : Subgroup G, IsPGroup 2 X → X ≤ rankThreePrimeCore p M →
      X ≤ Subgroup.centralizer ({x} : Set G) → X = ⊥ := by
  have _hU0 := hU0
  exact u3_cor47_gen hS hD1 (typeSigTrivOn_u3 hc.prime hc.five) (u3_S_decomp hc)
    (pointConfig_of_u3 hc)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
