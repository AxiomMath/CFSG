module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113c
public import CFSG.Goldschmidt.Steps.Sec82PGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut)
open scoped MatrixGroups Pointwise

namespace Lemma113d

open Lemma113c CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

section Quot

variable {H : Type} [Group H] {N : Subgroup H} [N.Normal]

theorem mk_eq_of_mul_inv_mem {a b : H} (h : a * b⁻¹ ∈ N) :
    (QuotientGroup.mk a : H ⧸ N) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq]
  have h2 := (inferInstance : N.Normal).conj_mem _ h b⁻¹
  have h3 : a⁻¹ * b = (b⁻¹ * (a * b⁻¹) * b⁻¹⁻¹)⁻¹ := by group
  rw [h3]
  exact N.inv_mem h2

theorem mul_inv_mem_of_mk_eq {a b : H} (h : (QuotientGroup.mk a : H ⧸ N) = QuotientGroup.mk b) :
    a * b⁻¹ ∈ N := by
  rw [QuotientGroup.eq] at h
  have h2 := (inferInstance : N.Normal).conj_mem _ (N.inv_mem h) a
  have h3 : a * (a⁻¹ * b)⁻¹ * a⁻¹ = a * b⁻¹ := by group
  rw [← h3]
  exact h2

end Quot

theorem mem_centBar_iff {Q L : Subgroup G} {g : G} :
    g ∈ centBar 3 Q L ↔ g ∈ Q ∧ ∃ γ : ↥(Subgroup.normalizer (L : Set G)),
      (γ : G) = g ∧ barAut 3 L γ = 1 := by
  unfold centBar
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨γ, hγ, rfl⟩, hQ⟩
    exact ⟨hQ, γ, rfl, MonoidHom.mem_ker.1 hγ⟩
  · rintro ⟨hQ, γ, rfl, hγ⟩
    exact ⟨⟨γ, MonoidHom.mem_ker.2 hγ, rfl⟩, hQ⟩

theorem smul_mul_inv_mem_core {L : Subgroup G} {γ : ↥(Subgroup.normalizer (L : Set G))}
    (hγ : barAut 3 L γ = 1) (x : ↥L) :
    L.normalizerMonoidHom γ x * x⁻¹ ∈ GLAPPrimeCore 3 ↥L := by
  have h1 : barAut 3 L γ (QuotientGroup.mk x) = QuotientGroup.mk x := by
    rw [hγ, MulAut.one_apply]
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h1
  exact mul_inv_mem_of_mk_eq h1

theorem card_inf_core {nL nQ nS nP m k q n : ℕ} (hLc : nL = 27 * m) (hm : ¬ 3 ∣ m)
    (hQc : nQ = 3 ^ q) (hPc : nP = 3 ^ n) (hk : ¬ 3 ∣ k) (hsupd : nS ∣ nQ * k)
    (hSpos : 0 < nS) (hprod : nS * nP = nL * nQ) (hPL : nP ∣ nL) : nP = 27 := by
  obtain ⟨s, r, hr, hsr⟩ := Nat.exists_eq_pow_mul_and_not_dvd hSpos.ne' 3 (by norm_num)
  have hsn : s + n = q + 3 := by
    apply pow_three_eq_of_mul (a := r) (b := m)
    · have : 3 ^ (s + n) * r = 3 ^ (q + 3) * m := by
        calc 3 ^ (s + n) * r = nS * nP := by rw [hsr, hPc, pow_add]; ring
          _ = nL * nQ := hprod
          _ = 27 * m * 3 ^ q := by rw [hLc, hQc]
          _ = 3 ^ (q + 3) * m := by rw [pow_add]; ring
      exact this
    · exact hr
    · exact hm
  have hsq : s ≤ q := by
    have hd : 3 ^ s ∣ nQ * k := by
      rw [hsr] at hsupd
      exact (Dvd.intro r rfl).trans hsupd
    rw [hQc] at hd
    have hcop : Nat.Coprime (3 ^ s) k := Nat.Coprime.pow_left s
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk)
    have h3 : 3 ^ s ∣ 3 ^ q := hcop.dvd_of_dvd_mul_right hd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h3
  have hnle : n ≤ 3 := by
    have hd : 3 ^ n ∣ 27 * m := by
      rw [← hLc, ← hPc]
      exact hPL
    have hcop : Nat.Coprime (3 ^ n) m := Nat.Coprime.pow_left n
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hm)
    have h3 : 3 ^ n ∣ 3 ^ 3 := by
      have := hcop.dvd_of_dvd_mul_right hd
      simpa using this
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h3
  have hn3 : 3 ≤ n := by omega
  have hn : n = 3 := le_antisymm hnle hn3
  rw [hPc, hn]
  norm_num

theorem card_inf_eq_27 {X L Q : Subgroup G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hLX : X ≤ Subgroup.normalizer (L : Set G)) (hLle : L ≤ X)
    (hL : IsLTwoTwentySeven (barOf 3 L)) :
    Nat.card ↥(Q ⊓ L : Subgroup G) = 27 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e0⟩ := hL
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQ.1.trans hLX
  have hcopO : Nat.Coprime 3 (Nat.card ↥(GLAPPrimeCore 3 ↥L)) :=
    CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥L
  have hnO : ¬ 3 ∣ Nat.card ↥(GLAPPrimeCore 3 ↥L) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcopO
  have hquot : Nat.card (↥L ⧸ GLAPPrimeCore 3 ↥L) = 9828 := by
    rw [Nat.card_congr e0.toEquiv, CFSG.RankThree.PartTwo.KFacts.card_psl2_27]
  have hLc : Nat.card ↥L = 27 * (364 * Nat.card ↥(GLAPPrimeCore 3 ↥L)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (GLAPPrimeCore 3 ↥L), hquot]
    ring
  have hm3 : ¬ 3 ∣ 364 * Nat.card ↥(GLAPPrimeCore 3 ↥L) := by
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h1 | h1
    · norm_num at h1
    · exact hnO h1
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hQN
  obtain ⟨q, hq⟩ := (IsPGroup.iff_card (p := 3)).1 hQ.2.1
  have hPp : IsPGroup 3 ↥(Q ⊓ L : Subgroup G) := hQ.2.1.to_le inf_le_left
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hPp
  obtain ⟨k, hXk, hk⟩ := isSylowIn_card_index hQ hQ1
  have hsup : Nat.card ↥(L ⊔ Q : Subgroup G) ∣ Nat.card ↥X :=
    Subgroup.card_dvd_of_le (sup_le hLle hQ.1)
  have hPL : Nat.card ↥(Q ⊓ L : Subgroup G) ∣ Nat.card ↥L :=
    Subgroup.card_dvd_of_le inf_le_right
  rw [inf_comm] at hprod
  have hprod' : Nat.card ↥(L ⊔ Q : Subgroup G) * Nat.card ↥(Q ⊓ L : Subgroup G) =
      Nat.card ↥L * Nat.card ↥Q := hprod
  rw [hXk] at hsup
  exact card_inf_core hLc hm3 hq hn hk hsup (Nat.card_pos) hprod' hPL

theorem isElemAbelian_of_map_injective {H K : Type} [Group H] [Group K] {p : ℕ} (f : H →* K)
    (hf : Function.Injective f) {S : Subgroup H} (hS : IsElemAbelian p (S.map f)) :
    IsElemAbelian p S := by
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    intro x hx y hy
    apply hf
    rw [map_mul, map_mul]
    exact congrArg Subtype.val
      (hS.1.is_comm.comm ⟨f x, Subgroup.mem_map_of_mem f hx⟩ ⟨f y, Subgroup.mem_map_of_mem f hy⟩)
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, fun x hx => ?_⟩
  apply hf
  rw [map_pow, map_one]
  exact hS.2 _ (Subgroup.mem_map_of_mem f hx)

theorem isElemAbelian_inf {X L Q : Subgroup G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hLX : X ≤ Subgroup.normalizer (L : Set G)) (hLle : L ≤ X)
    (hL : IsLTwoTwentySeven (barOf 3 L)) :
    IsElemAbelian 3 (Q ⊓ L : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥(Q ⊓ L : Subgroup G) = 27 := card_inf_eq_27 hQ hQ1 hLX hLle hL
  obtain ⟨e0⟩ := hL
  have hPL : Q ⊓ L ≤ L := inf_le_right
  have hPp : IsPGroup 3 ↥(Q ⊓ L : Subgroup G) := hQ.2.1.to_le inf_le_left
  have hPLp : IsPGroup 3 ↥((Q ⊓ L : Subgroup G).subgroupOf L) :=
    hPp.of_injective (Subgroup.subgroupOfEquivOfLe hPL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hPL).injective
  have hφinj := quot_injective hPL hPp
  set φ := (QuotientGroup.mk' (GLAPPrimeCore 3 ↥L)).comp
    ((Q ⊓ L : Subgroup G).subgroupOf L).subtype with hφdef
  have hRc : Nat.card φ.range = 27 := by
    rw [← hcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm.trans
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL).toEquiv)
  have hbar : Nat.card (↥L ⧸ GLAPPrimeCore 3 ↥L) = 9828 := by
    rw [Nat.card_congr e0.toEquiv, CFSG.RankThree.PartTwo.KFacts.card_psl2_27]
  have hRidx : ¬ 3 ∣ φ.range.index := by
    have h1 := Subgroup.card_mul_index φ.range
    rw [hRc, hbar] at h1
    have h2 : φ.range.index = 364 := by omega
    rw [h2]
    norm_num
  obtain ⟨E0, hE0el, hE0c⟩ := psl2_27_sylow e0
  have hEidx : ¬ 3 ∣ E0.index := by
    have h1 := Subgroup.card_mul_index E0
    rw [hE0c, hbar] at h1
    have h2 : E0.index = 364 := by omega
    rw [h2]
    norm_num
  have hRp : IsPGroup 3 ↥φ.range :=
    hPLp.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hRel : IsElemAbelian 3 φ.range := isElemAbelian_of_sylow_conj hE0el hRp hRidx hEidx
  have hTop : IsElemAbelian 3 (⊤ : Subgroup ↥((Q ⊓ L : Subgroup G).subgroupOf L)) := by
    apply isElemAbelian_of_map_injective φ hφinj
    rw [← MonoidHom.range_eq_map]
    exact hRel
  have hψ : Function.Injective (L.subtype.comp ((Q ⊓ L : Subgroup G).subgroupOf L).subtype) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  have hψrange : (⊤ : Subgroup ↥((Q ⊓ L : Subgroup G).subgroupOf L)).map
      (L.subtype.comp ((Q ⊓ L : Subgroup G).subgroupOf L).subtype) = Q ⊓ L := by
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩
      exact Subgroup.mem_subgroupOf.1 w.2
    · intro hz
      exact ⟨⟨⟨z, hz.2⟩, Subgroup.mem_subgroupOf.2 hz⟩, trivial, rfl⟩
  have hfin := isElemAbelian_map_of_injective _ hψ hTop
  rw [hψrange] at hfin
  exact hfin

theorem isPGroup_subgroupOf_inf {Q L : Subgroup G} (hQp : IsPGroup 3 ↥Q) :
    IsPGroup 3 ↥((Q ⊓ L : Subgroup G).subgroupOf L) :=
  (hQp.to_le inf_le_left).of_injective (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ⊓ L ≤ L)).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe (inf_le_right : Q ⊓ L ≤ L)).injective

theorem inf_centBar_eq_bot {X L Q : Subgroup G} (hQ : IsSylowIn 3 X Q)
    (hLX : X ≤ Subgroup.normalizer (L : Set G)) (hL : IsLTwoTwentySeven (barOf 3 L)) :
    (Q ⊓ L : Subgroup G) ⊓ centBar 3 Q L = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e0⟩ := hL
  have hP' := isPGroup_subgroupOf_inf (L := L) hQ.2.1
  rw [eq_bot_iff]
  rintro q ⟨⟨hqQ, hqL⟩, hqc⟩
  obtain ⟨-, γ, hγq, hγ⟩ := mem_centBar_iff.1 hqc
  set q' : ↥L := ⟨q, hqL⟩ with hq'
  have hcomm : ∀ x : ↥L, (QuotientGroup.mk q' : ↥L ⧸ GLAPPrimeCore 3 ↥L) * QuotientGroup.mk x =
      QuotientGroup.mk x * QuotientGroup.mk q' := by
    intro x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    apply mk_eq_of_mul_inv_mem
    have hx := smul_mul_inv_mem_core hγ x
    have hconj : L.normalizerMonoidHom γ x = q' * x * q'⁻¹ := by
      apply Subtype.ext
      simp [hγq, hq']
    have heq : q' * x * (x * q')⁻¹ = L.normalizerMonoidHom γ x * x⁻¹ := by
      rw [hconj]
      group
    rw [heq]
    exact hx
  have hz : (QuotientGroup.mk q' : ↥L ⧸ GLAPPrimeCore 3 ↥L) = 1 := by
    apply psl2_27_centre e0
    intro s
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore 3 ↥L) s
    exact (hcomm x).symm
  have hq1 : q' = 1 := by
    have hO : q' ∈ GLAPPrimeCore 3 ↥L := (QuotientGroup.eq_one_iff q').1 hz
    have hmem : q' ∈ GLAPPrimeCore 3 ↥L ⊓ ((Q ⊓ L : Subgroup G).subgroupOf L) :=
      ⟨hO, Subgroup.mem_subgroupOf.2 ⟨hqQ, hqL⟩⟩
    rw [core_inf_eq_bot hP', Subgroup.mem_bot] at hmem
    exact hmem
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hq1

theorem commute_of_mem_centBar {X L Q : Subgroup G} (hQ : IsSylowIn 3 X Q)
    {u q : G} (hu : u ∈ centBar 3 Q L) (hq : q ∈ Q ⊓ L) : u * q = q * u := by
  classical
  have hP' := isPGroup_subgroupOf_inf (L := L) hQ.2.1
  obtain ⟨huQ, γ, hγu, hγ⟩ := mem_centBar_iff.1 hu
  have huL : u ∈ Subgroup.normalizer (L : Set G) := hγu ▸ γ.2
  set x : ↥L := ⟨q, hq.2⟩ with hx
  have hc := smul_mul_inv_mem_core hγ x
  have hkey : ((L.normalizerMonoidHom γ x * x⁻¹ : ↥L) : G) = u * q * u⁻¹ * q⁻¹ := by
    simp [hγu, hx]
  have hconjL : u * q * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 huL q).1 hq.2
  have hcP : L.normalizerMonoidHom γ x * x⁻¹ ∈
      GLAPPrimeCore 3 ↥L ⊓ ((Q ⊓ L : Subgroup G).subgroupOf L) := by
    refine ⟨hc, Subgroup.mem_subgroupOf.2 ?_⟩
    rw [hkey]
    exact ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem huQ hq.1) (Q.inv_mem huQ)) (Q.inv_mem hq.1),
      L.mul_mem hconjL (L.inv_mem hq.2)⟩
  rw [core_inf_eq_bot hP', Subgroup.mem_bot] at hcP
  have hfin : u * q * u⁻¹ * q⁻¹ = 1 := by
    rw [← hkey, hcP]
    rfl
  calc u * q = (u * q * u⁻¹ * q⁻¹) * (q * u) := by group
    _ = q * u := by rw [hfin, one_mul]

theorem centBar_normal {L Q : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (L : Set G)) {q u : G}
    (hq : q ∈ Q) (hu : u ∈ centBar 3 Q L) : q * u * q⁻¹ ∈ centBar 3 Q L := by
  obtain ⟨huQ, γ, hγu, hγ⟩ := mem_centBar_iff.1 hu
  rw [mem_centBar_iff]
  refine ⟨Q.mul_mem (Q.mul_mem hq huQ) (Q.inv_mem hq),
    ⟨q, hQN hq⟩ * γ * (⟨q, hQN hq⟩)⁻¹, ?_, ?_⟩
  · simp [hγu]
  · simp [map_mul, map_inv, hγ]

theorem mem_normalizer_sup {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

theorem mem_normalizer_inf {Q L : Subgroup G} {q : G} (hq : q ∈ Q)
    (hqL : q ∈ Subgroup.normalizer (L : Set G)) :
    q ∈ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Q, g ∈ Subgroup.normalizer (L : Set G) →
      ∀ h ∈ Q ⊓ L, g * h * g⁻¹ ∈ Q ⊓ L := by
    intro g hg hgL h hh
    exact ⟨Q.mul_mem (Q.mul_mem hg hh.1) (Q.inv_mem hg),
      (Subgroup.mem_normalizer_iff.1 hgL h).1 hh.2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact key q hq hqL h hh
  · intro hh
    have := key q⁻¹ (Q.inv_mem hq) (Subgroup.inv_mem _ hqL) (q * h * q⁻¹) hh
    have e : q⁻¹ * (q * h * q⁻¹) * q⁻¹⁻¹ = h := by group
    rw [e] at this
    exact this


theorem claim113A_clause4 {X L Q M : Subgroup G} {a : G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hLX : X ≤ Subgroup.normalizer (L : Set G)) (hLle : L ≤ X)
    (hL : IsLTwoTwentySeven (barOf 3 L)) (hQM : Q ≤ M) (ha : a ∈ Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    IsCyclic ↥(centBar 3 Q L) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQN : Q ≤ Subgroup.normalizer (L : Set G) := hQ.1.trans hLX
  have hRQ : centBar 3 Q L ≤ Q := fun g hg => (mem_centBar_iff.1 hg).1
  have hTR : Q ≤ Subgroup.normalizer ((centBar 3 Q L : Subgroup G) : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact centBar_normal hQN hq hh
    · intro hh
      have := centBar_normal hQN (Q.inv_mem hq) hh
      have e : q⁻¹ * (q * h * q⁻¹) * q⁻¹⁻¹ = h := by group
      rw [e] at this
      exact this
  by_contra hc
  obtain ⟨V, hVR, hVn, hVcard, hVexp, hVcomm⟩ :=
    CFSG.Goldschmidt.Sec82.exists_normal_plane_le_of_le Nat.prime_three (by norm_num)
      hQ.2.1 hRQ hTR hc
  have hVel : IsElemAbelian 3 V :=
    ⟨⟨⟨fun x y => Subtype.ext (hVcomm x.1 x.2 y.1 y.2)⟩⟩, hVexp⟩
  have hQ0el : IsElemAbelian 3 (Q ⊓ L : Subgroup G) := isElemAbelian_inf hQ hQ1 hLX hLle hL
  have hVQ0 : ∀ v ∈ V, ∀ x ∈ (Q ⊓ L : Subgroup G), v * x = x * v := fun v hv x hx =>
    commute_of_mem_centBar hQ (hVR hv) hx
  have hQ0c : (Q ⊓ L : Subgroup G) ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 (fun v hv => hVQ0 v hv x hx)
  have hVQ0N : V ≤ Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) := fun v hv =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.2 (fun x hx => (hVQ0 v hv x hx).symm))
  have hE1el : IsElemAbelian 3 ((Q ⊓ L : Subgroup G) ⊔ V) :=
    isElemAbelian_sup_of_commute hQ0el hVel hQ0c
  have hQ0card : Nat.card ↥(Q ⊓ L : Subgroup G) = 27 := card_inf_eq_27 hQ hQ1 hLX hLle hL
  have hinter : (Q ⊓ L : Subgroup G) ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx2 : x ∈ (Q ⊓ L : Subgroup G) ⊓ centBar 3 Q L :=
      ⟨hx.1, hVR hx.2⟩
    rw [inf_centBar_eq_bot hQ hLX hL, Subgroup.mem_bot] at hx2
    rw [hx2]
    exact Subgroup.one_mem _
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hVQ0N
  rw [hinter, Subgroup.card_bot, hQ0card, hVcard] at hprod
  have hE1card : Nat.card ↥((Q ⊓ L : Subgroup G) ⊔ V) = 3 ^ 5 := by
    rw [mul_one] at hprod
    rw [hprod]
    norm_num
  have hE1Q : (Q ⊓ L : Subgroup G) ⊔ V ≤ Q := sup_le inf_le_left (hVR.trans hRQ)
  have hE1M : (Q ⊓ L : Subgroup G) ⊔ V ≤ M := hE1Q.trans hQM
  have hE1n : Q ≤ Subgroup.normalizer (((Q ⊓ L : Subgroup G) ⊔ V : Subgroup G) : Set G) :=
    fun q hq => mem_normalizer_sup (mem_normalizer_inf hq (hQN hq)) (hVn hq)
  have h5 : 5 ≤ CFSG.Open.pRank 3 ((Q ⊓ L : Subgroup G) ⊔ V) :=
    (l113_pRank_eq hE1el hE1card).ge
  exact h0 _ hE1M hE1el h5 (hE1n ha)

open CFSG.GorensteinWalter in
@[expose] def Input113dCentralizer27 : Prop :=
  ∀ (Y : Type) [Group Y] (e : Y ≃* PSL2 (GaloisField 3 3)) (σ : MulAut Y)
    (U : Subgroup (MulAut Y)),
    σ ∈ Subgroup.normalizer (U : Set (MulAut Y)) → σ ^ 3 = 1 →
    σ ∉ (MulAut.conj : Y →* MulAut Y).range → U ≤ (MulAut.conj : Y →* MulAut Y).range →
    IsElemAbelian 3 U → Nat.card U = 27 →
    Nat.card ↥(U ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y))) ≤ 3

section AutLayer

open CFSG.GorensteinWalter

variable {Y : Type} [Group Y] [Finite Y]

theorem innerAut_normal : ((MulAut.conj : Y →* MulAut Y).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨y, rfl⟩ := hn
  refine ⟨g y, ?_⟩
  ext z
  simp [MulAut.conj_apply, mul_assoc]

theorem conj_injective_of_centre_trivial (hZ : ∀ z : Y, (∀ s : Y, s * z = z * s) → z = 1) :
    Function.Injective (MulAut.conj : Y →* MulAut Y) := by
  intro a b h
  have hz : a⁻¹ * b ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h' := DFunLike.congr_fun h g
    simp only [MulAut.conj_apply] at h'
    calc g * (a⁻¹ * b) = a⁻¹ * (a * g * a⁻¹) * b := by group
      _ = a⁻¹ * (b * g * b⁻¹) * b := by rw [h']
      _ = a⁻¹ * b * g := by group
  have := hZ (a⁻¹ * b) (fun s => (Subgroup.mem_center_iff.1 hz) s)
  exact inv_mul_eq_one.1 this

theorem card_innerAut_eq {e : Y ≃* PSL2 (GaloisField 3 3)} :
    Nat.card ↥((MulAut.conj : Y →* MulAut Y).range) = 9828 := by
  have hinj := conj_injective_of_centre_trivial (fun z hz => psl2_27_centre e z hz)
  have h1 : Nat.card Y = Nat.card ↥((MulAut.conj : Y →* MulAut Y).range) :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [← h1, Nat.card_congr e.toEquiv, CFSG.RankThree.PartTwo.KFacts.card_psl2_27]

theorem card_le_27_of_isPGroup_inner {e : Y ≃* PSL2 (GaloisField 3 3)}
    {P : Subgroup (MulAut Y)} (hP : IsPGroup 3 P)
    (hPi : P ≤ (MulAut.conj : Y →* MulAut Y).range) : Nat.card P ≤ 27 := by
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).1 hP
  have hdvd : Nat.card P ∣ 9828 := by
    rw [← card_innerAut_eq (e := e)]
    exact Subgroup.card_dvd_of_le hPi
  rw [hn] at hdvd ⊢
  have h3n : 3 ^ n ∣ 27 * 364 := by
    have : (27 : ℕ) * 364 = 9828 := by norm_num
    rw [this]
    exact hdvd
  have hcop : Nat.Coprime (3 ^ n) 364 :=
    Nat.Coprime.pow_left n (by norm_num)
  have h27 : 3 ^ n ∣ 27 := hcop.dvd_of_dvd_mul_right h3n
  have hn3 : n ≤ 3 := by
    have h' : 3 ^ n ∣ 3 ^ 3 := by simpa using h27
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).1 h'
  calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 27 := by norm_num

theorem le_normalizer_inf_of_normal {M : Type} [Group M] {I : Subgroup M} [I.Normal]
    (R : Subgroup M) : R ≤ Subgroup.normalizer ((R ⊓ I : Subgroup M) : Set M) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨hhR, hhI⟩
    exact ⟨R.mul_mem (R.mul_mem hr hhR) (R.inv_mem hr), (inferInstance : I.Normal).conj_mem h hhI r⟩
  · rintro ⟨hhR, hhI⟩
    have hr' := R.inv_mem hr
    refine ⟨?_, ?_⟩
    · have := R.mul_mem (R.mul_mem hr' hhR) (R.inv_mem hr')
      simpa [mul_assoc] using this
    · have := (inferInstance : I.Normal).conj_mem _ hhI r⁻¹
      simpa [mul_assoc] using this

theorem inner_of_elemAbelian (hC : Input113dCentralizer27) {e : Y ≃* PSL2 (GaloisField 3 3)}
    {R S : Subgroup (MulAut Y)} (hR81 : Nat.card R ≤ 81)
    (hU : IsElemAbelian 3 (R ⊓ (MulAut.conj : Y →* MulAut Y).range))
    (hU27 : Nat.card ↥(R ⊓ (MulAut.conj : Y →* MulAut Y).range) = 27)
    (hS : IsElemAbelian 3 S) (hSR : S ≤ R) (hS27 : 27 ≤ Nat.card S) :
    S ≤ (MulAut.conj : Y →* MulAut Y).range := by
  classical
  by_contra hcon
  obtain ⟨σ, hσS, hσI⟩ := SetLike.not_le_iff_exists.1 hcon
  set I : Subgroup (MulAut Y) := (MulAut.conj : Y →* MulAut Y).range with hIdef
  haveI : I.Normal := innerAut_normal
  set U : Subgroup (MulAut Y) := R ⊓ I with hUdef
  have hσR : σ ∈ R := hSR hσS
  have hSN : S ≤ Subgroup.normalizer (U : Set (MulAut Y)) := fun s hs =>
    le_normalizer_inf_of_normal R (hSR hs)
  have hUnorm : σ ∈ Subgroup.normalizer (U : Set (MulAut Y)) := hSN hσS
  have hσ3 : σ ^ 3 = 1 := hS.2 σ hσS
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hSN
  have hsup_le : Nat.card ↥(U ⊔ S) ≤ 81 :=
    (Subgroup.card_le_of_le (sup_le inf_le_left hSR)).trans hR81
  rw [hU27] at hcard
  have hinf9 : 9 ≤ Nat.card ↥(U ⊓ S) := by
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card ↥(U ⊓ S) ≤ 8 := by omega
    have h2 : Nat.card ↥(U ⊔ S) * Nat.card ↥(U ⊓ S) ≤ 81 * 8 :=
      Nat.mul_le_mul hsup_le h1
    have h3 : 27 * 27 ≤ 27 * Nat.card S := Nat.mul_le_mul_left 27 hS27
    omega
  have hsub : U ⊓ S ≤ U ⊓ Subgroup.centralizer ({σ} : Set (MulAut Y)) := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    show t ∈ Subgroup.centralizer ({σ} : Set (MulAut Y))
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact congrArg Subtype.val (hS.1.is_comm.comm ⟨σ, hσS⟩ ⟨t, ht.2⟩)
  have hle := Subgroup.card_le_of_le hsub
  have hC' := hC Y e σ U hUnorm hσ3 hσI inf_le_right hU hU27
  omega

end AutLayer

theorem isElemAbelian_top {H : Type} [Group H] {p : ℕ} {S : Subgroup H}
    (hS : IsElemAbelian p S) : IsElemAbelian p (⊤ : Subgroup ↥S) := by
  have hc : ∀ a b : ↥S, a * b = b * a := fun a b =>
    Subtype.ext (congrArg Subtype.val (hS.1.is_comm.comm ⟨a.1, a.2⟩ ⟨b.1, b.2⟩))
  refine ⟨⟨⟨fun x y => Subtype.ext (hc x.1 y.1)⟩⟩, fun x _ => Subtype.ext ?_⟩
  simpa using hS.2 _ x.2

theorem isElemAbelian_map_any {H K' : Type} [Group H] [Group K'] {p : ℕ} (f : H →* K')
    {S : Subgroup H} (hS : IsElemAbelian p S) : IsElemAbelian p (S.map f) := by
  have hcomm : ∀ x ∈ S.map f, ∀ y ∈ S.map f, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg f (congrArg Subtype.val (hS.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
  refine ⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_pow, hS.2 a ha, map_one]

section RhoLayer

variable {K Q : Subgroup G}

theorem barAut_eq_conj {q : G} (hqK : q ∈ K) (hqN : q ∈ Subgroup.normalizer (K : Set G)) :
    barAut 3 K ⟨q, hqN⟩ = MulAut.conj (QuotientGroup.mk ⟨q, hqK⟩ : barOf 3 K) := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply]
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1

@[expose] noncomputable def rhoQ (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    ↥Q →* MulAut (barOf 3 K) :=
  (barAut 3 K).comp (Subgroup.inclusion hQK)

theorem rhoQ_apply (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (q : ↥Q) :
    rhoQ hQK q = barAut 3 K ⟨q.1, hQK q.2⟩ := rfl

theorem rhoQ_eq_one_iff (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (q : ↥Q) :
    rhoQ hQK q = 1 ↔ (q : G) ∈ centBar 3 Q K := by
  rw [mem_centBar_iff]
  constructor
  · intro h
    exact ⟨q.2, ⟨q.1, hQK q.2⟩, rfl, by rw [rhoQ_apply] at h; exact h⟩
  · rintro ⟨-, γ, hγ, hγ1⟩
    have hγq : γ = ⟨q.1, hQK q.2⟩ := Subtype.ext hγ
    rw [rhoQ_apply, ← hγq]
    exact hγ1

theorem rhoQ_mem_inner (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (q : ↥Q) (hq : (q : G) ∈ K) :
    rhoQ hQK q ∈ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range := by
  rw [rhoQ_apply, barAut_eq_conj hq (hQK q.2)]
  exact ⟨_, rfl⟩

end RhoLayer

section RhoLayer2

variable {X K Q : Subgroup G}

@[expose] noncomputable def Ubar (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup (MulAut (barOf 3 K)) :=
  ((rhoQ hQK).comp ((Q ⊓ K : Subgroup G).subgroupOf Q).subtype).range

theorem Ubar_le_range (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Ubar hQK ≤ (rhoQ hQK).range := by
  rintro _ ⟨d, rfl⟩
  exact ⟨_, rfl⟩

theorem Ubar_le_inner (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Ubar hQK ≤ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range := by
  rintro _ ⟨d, rfl⟩
  exact rhoQ_mem_inner hQK _ (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 d.2)).2

theorem Ubar_card (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) (hXN : X ≤ Subgroup.normalizer (K : Set G))
    (hKX : K ≤ X) (hK : IsLTwoTwentySeven (barOf 3 K)) :
    Nat.card ↥(Ubar (hQ.1.trans hXN)) = 27 := by
  classical
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hinj : Function.Injective
      ((rhoQ hQK).comp ((Q ⊓ K : Subgroup G).subgroupOf Q).subtype) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hd' : rhoQ hQK ((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : ↥Q) = 1 := hd
    rw [rhoQ_eq_one_iff] at hd'
    have hmem : (((d : ↥((Q ⊓ K : Subgroup G).subgroupOf Q)) : ↥Q) : G) ∈
        (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K :=
      ⟨Subgroup.mem_subgroupOf.1 d.2, hd'⟩
    rw [inf_centBar_eq_bot hQ hXN hK, Subgroup.mem_bot] at hmem
    apply Subtype.ext
    apply Subtype.ext
    exact hmem
  have hcard_dom : Nat.card ↥((Q ⊓ K : Subgroup G).subgroupOf Q) = 27 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Q ⊓ K ≤ Q)).toEquiv]
    exact card_inf_eq_27 hQ hQ1 hXN hKX hK
  unfold Ubar
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcard_dom]

theorem Ubar_elemAbelian (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X) (hK : IsLTwoTwentySeven (barOf 3 K)) :
    IsElemAbelian 3 (Ubar (hQ.1.trans hXN)) := by
  have hQKel : IsElemAbelian 3 (Q ⊓ K : Subgroup G) := isElemAbelian_inf hQ hQ1 hXN hKX hK
  have hD : IsElemAbelian 3 ((Q ⊓ K : Subgroup G).subgroupOf Q) := by
    apply isElemAbelian_of_map_injective Q.subtype Q.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 inf_le_left]
    exact hQKel
  unfold Ubar
  rw [MonoidHom.range_eq_map]
  exact isElemAbelian_map_any _ (isElemAbelian_top hD)

theorem rhoQ_range_isPGroup (hQp : IsPGroup 3 ↥Q) (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    IsPGroup 3 ↥(rhoQ hQK).range :=
  hQp.of_surjective (rhoQ hQK).rangeRestrict (rhoQ hQK).rangeRestrict_surjective

theorem rhoQ_range_card_le (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hQp : IsPGroup 3 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) : Nat.card ↥(rhoQ hQK).range ≤ 81 :=
  CFSG.RankThree.PartTwo.KFacts.card_le_of_isPGroup_three_mulAut e0 (rhoQ_range_isPGroup hQp hQK)

theorem inf_inner_eq_Ubar (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hQp : IsPGroup 3 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hU27 : Nat.card ↥(Ubar hQK) = 27) :
    (rhoQ hQK).range ⊓ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range = Ubar hQK := by
  have hle : Ubar hQK ≤ (rhoQ hQK).range ⊓ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range :=
    le_inf (Ubar_le_range hQK) (Ubar_le_inner hQK)
  have hP : IsPGroup 3 ↥((rhoQ hQK).range ⊓
      (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range) :=
    (rhoQ_range_isPGroup hQp hQK).to_le inf_le_left
  have h27 := card_le_27_of_isPGroup_inner (e := e0) hP inf_le_right
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hU27]; exact h27)).symm

theorem mem_sup_of_rho_inner (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hQp : IsPGroup 3 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hU27 : Nat.card ↥(Ubar hQK) = 27)
    (f : ↥Q) (hf : rhoQ hQK f ∈ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range) :
    (f : G) ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
  have hR : rhoQ hQK f ∈ (rhoQ hQK).range ⊓
      (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range :=
    ⟨⟨f, rfl⟩, hf⟩
  rw [inf_inner_eq_Ubar e0 hQp hQK hU27] at hR
  obtain ⟨d, hd⟩ := hR
  have hd' : rhoQ hQK (d.1 : ↥Q) = rhoQ hQK f := hd
  have h1 : rhoQ hQK ((d.1 : ↥Q)⁻¹ * f) = 1 := by
    rw [map_mul, map_inv, hd', inv_mul_cancel]
  have h2 : (((d.1 : ↥Q)⁻¹ * f : ↥Q) : G) ∈ centBar 3 Q K := (rhoQ_eq_one_iff hQK _).1 h1
  have hdK : (d.1 : G) ∈ (Q ⊓ K : Subgroup G) := Subgroup.mem_subgroupOf.1 d.2
  have hsplit : (f : G) = (d.1 : G) * (((d.1 : ↥Q)⁻¹ * f : ↥Q) : G) := by
    simp
  rw [hsplit]
  exact Subgroup.mul_mem_sup hdK h2

theorem card_ker_rhoQ (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(rhoQ hQK).ker = Nat.card ↥(centBar 3 Q K) := by
  have hmap : ((rhoQ hQK).ker).map Q.subtype = centBar 3 Q K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (rhoQ_eq_one_iff hQK y).1 (MonoidHom.mem_ker.1 hy)
    · intro hx
      exact ⟨⟨x, (mem_centBar_iff.1 hx).1⟩, MonoidHom.mem_ker.2 ((rhoQ_eq_one_iff hQK _).2 hx), rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective Q.subtype_injective]

theorem card_le_81_mul_centBar (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hQp : IsPGroup 3 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥Q ≤ 81 * Nat.card ↥(centBar 3 Q K) := by
  have hR := rhoQ_range_card_le e0 hQp hQK
  calc Nat.card ↥Q = Nat.card ↥(centBar 3 Q K) * Nat.card ↥(rhoQ hQK).range := by
        rw [CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range (rhoQ hQK),
          card_ker_rhoQ hQK]
    _ ≤ Nat.card ↥(centBar 3 Q K) * 81 := Nat.mul_le_mul_left _ hR
    _ = 81 * Nat.card ↥(centBar 3 Q K) := mul_comm _ _

end RhoLayer2

section Cyclic

theorem card_le_three_of_sub_cyclic {C W : Subgroup G} (hC : IsCyclic ↥C) (hWC : W ≤ C)
    (hW : IsElemAbelian 3 W) : Nat.card ↥W ≤ 3 := by
  classical
  haveI := hC
  have hcard : Nat.card ↥(W.subgroupOf C) = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWC).toEquiv
  rw [← hcard]
  have hexp : Monoid.exponent ↥(W.subgroupOf C) ∣ 3 := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro x
    apply Subtype.ext
    apply Subtype.ext
    simpa using hW.2 _ (Subgroup.mem_subgroupOf.1 x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  exact Nat.le_of_dvd (by norm_num) hexp

theorem mem_zpowers_of_pow_three_of_cyclic {C : Subgroup G} (hC : IsCyclic ↥C) {e c : G}
    (heC : e ∈ C) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (hcC : c ∈ C) (hc3 : c ^ 3 = 1) :
    c ∈ Subgroup.zpowers e := by
  classical
  haveI := hC
  have hcomm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a := by
    intro a ha b hb
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨b, hb⟩)
    have hcm : Commute (g ^ i) (g ^ j) := (Commute.refl g).zpow_zpow i j
    have h3 : (⟨a, ha⟩ : ↥C) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj]
      exact hcm.eq
    exact congrArg Subtype.val h3
  have hW : IsElemAbelian 3 (Subgroup.zpowers c ⊔ Subgroup.zpowers e) := by
    apply isElemAbelian_sup_of_commute (l113_isElemAbelian_zpowers hc3)
      (l113_isElemAbelian_zpowers he3)
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact l113_mem_centralizer_zpowers (hcomm e heC (c ^ k) (C.zpow_mem hcC k))
  have hWC : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤ C :=
    sup_le (Subgroup.zpowers_le.2 hcC) (Subgroup.zpowers_le.2 heC)
  have hle := card_le_three_of_sub_cyclic hC hWC hW
  have hecard : Nat.card ↥(Subgroup.zpowers e) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime he3 he1]
  have hsub : Subgroup.zpowers e ≤ Subgroup.zpowers c ⊔ Subgroup.zpowers e := le_sup_right
  have hcardle : Nat.card ↥(Subgroup.zpowers c ⊔ Subgroup.zpowers e) ≤
      Nat.card ↥(Subgroup.zpowers e) := by
    rw [hecard]
    exact hle
  have heq : Subgroup.zpowers e = Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
    Subgroup.eq_of_le_of_card_ge hsub hcardle
  have hc_mem : c ∈ Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers c)
  rw [← heq] at hc_mem
  exact hc_mem

end Cyclic

section RankQ

variable {K Q : Subgroup G}

theorem le_sup_of_elemAbelian_card_ge (hC : Input113dCentralizer27)
    (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hQp : IsPGroup 3 ↥Q)
    (hQK : Q ≤ Subgroup.normalizer (K : Set G)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    (hU : IsElemAbelian 3 (Ubar hQK)) (hU27 : Nat.card ↥(Ubar hQK) = 27)
    {F : Subgroup G} (hFQ : F ≤ Q) (hF : IsElemAbelian 3 F) (hF81 : 81 ≤ Nat.card ↥F) :
    F ≤ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
  classical
  set GF : Subgroup ↥Q := F.subgroupOf Q with hGF
  have hGFel : IsElemAbelian 3 GF := by
    apply isElemAbelian_of_map_injective Q.subtype Q.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hFQ]
    exact hF
  set f : ↥GF →* MulAut (barOf 3 K) := (rhoQ hQK).comp GF.subtype with hf
  set S : Subgroup (MulAut (barOf 3 K)) := f.range with hS
  have hSel : IsElemAbelian 3 S := by
    rw [hS, MonoidHom.range_eq_map]
    exact isElemAbelian_map_any _ (isElemAbelian_top hGFel)
  have hSR : S ≤ (rhoQ hQK).range := by
    rintro _ ⟨d, rfl⟩
    exact ⟨_, rfl⟩
  have hinj : Function.Injective (Q.subtype.comp GF.subtype : ↥GF →* G) :=
    fun a b h => Subtype.ext (Subtype.ext h)
  have hkerle : Nat.card ↥f.ker ≤ 3 := by
    set W : Subgroup G := f.ker.map (Q.subtype.comp GF.subtype : ↥GF →* G) with hW
    have hWcard : Nat.card ↥W = Nat.card ↥f.ker := Subgroup.card_map_of_injective hinj
    have hWC : W ≤ centBar 3 Q K := by
      rintro _ ⟨y, hy, rfl⟩
      exact (rhoQ_eq_one_iff hQK _).1 (MonoidHom.mem_ker.1 hy)
    have hWF : W ≤ F := by
      rintro _ ⟨y, _, rfl⟩
      exact Subgroup.mem_subgroupOf.1 y.2
    have hWel : IsElemAbelian 3 W := isElemAbelian_mono hF hWF
    rw [← hWcard]
    exact card_le_three_of_sub_cyclic hcyc hWC hWel
  have hcardF : Nat.card ↥F = Nat.card ↥GF :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFQ).toEquiv).symm
  have hkey : Nat.card ↥GF = Nat.card ↥f.ker * Nat.card ↥S :=
    CFSG.RankThree.PartTwo.KFacts.card_eq_card_ker_mul_card_range f
  have hS27 : 27 ≤ Nat.card ↥S := by
    have h1 : Nat.card ↥f.ker * Nat.card ↥S ≤ 3 * Nat.card ↥S := Nat.mul_le_mul_right _ hkerle
    omega
  have hR81 : Nat.card ↥(rhoQ hQK).range ≤ 81 := rhoQ_range_card_le e0 hQp hQK
  have hU' : IsElemAbelian 3 ((rhoQ hQK).range ⊓
      (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range) := by
    rw [inf_inner_eq_Ubar e0 hQp hQK hU27]
    exact hU
  have hU27' : Nat.card ↥((rhoQ hQK).range ⊓
      (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range) = 27 := by
    rw [inf_inner_eq_Ubar e0 hQp hQK hU27]
    exact hU27
  have hSinner : S ≤ (MulAut.conj : barOf 3 K →* MulAut (barOf 3 K)).range :=
    inner_of_elemAbelian (e := e0) hC hR81 hU' hU27' hSel hSR hS27
  intro x hx
  have hxQ : x ∈ Q := hFQ hx
  have hmem : rhoQ hQK ⟨x, hxQ⟩ ∈ S := ⟨⟨⟨x, hxQ⟩, Subgroup.mem_subgroupOf.2 hx⟩, rfl⟩
  exact mem_sup_of_rho_inner e0 hQp hQK hU27 ⟨x, hxQ⟩ (hSinner hmem)

end RankQ

section Structure

variable {K Q : Subgroup G}

theorem barAut_eq_one_of_centralizes {q : G} (hqN : q ∈ Subgroup.normalizer (K : Set G))
    (hq : ∀ x ∈ K, q * x = x * q) : barAut 3 K ⟨q, hqN⟩ = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  show q * (x : G) * q⁻¹ = x
  rw [hq (x : G) x.2]
  group

theorem e_mem_centBar {X : Subgroup G} {e : G} (hQ : IsSylowIn 3 X Q)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKe : ∀ x ∈ K, e * x = x * e)
    (heQ : e ∈ Q) : e ∈ centBar 3 Q K := by
  rw [mem_centBar_iff]
  have hN : e ∈ Subgroup.normalizer (K : Set G) := hXN (hQ.1 heQ)
  exact ⟨heQ, ⟨e, hN⟩, rfl, barAut_eq_one_of_centralizes hN hKe⟩

theorem elemAbelian_sup_zpowers {X : Subgroup G} {e : G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hKe : ∀ x ∈ K, e * x = x * e)
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q) :
    IsElemAbelian 3 ((Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e) ∧
      Nat.card ↥((Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e) = 81 := by
  classical
  have hK0 : IsElemAbelian 3 (Q ⊓ K : Subgroup G) := isElemAbelian_inf hQ hQ1 hXN hKX hK
  have hEe : IsElemAbelian 3 (Subgroup.zpowers e) := l113_isElemAbelian_zpowers he3
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
    intro x hx
    exact l113_mem_centralizer_zpowers (hKe x hx.2)
  have hcent' : Subgroup.zpowers e ≤ Subgroup.centralizer ((Q ⊓ K : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 (fun h hh => (hKe h hh.2).symm))
  have hel : IsElemAbelian 3 ((Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e) :=
    isElemAbelian_sup_of_commute hK0 hEe hcent
  have hinf : (Q ⊓ K : Subgroup G) ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxe : x ∈ centBar 3 Q K := by
      have he' : e ∈ centBar 3 Q K := e_mem_centBar hQ hXN hKe heQ
      exact (Subgroup.zpowers_le.2 he') hx.2
    have hx2 : x ∈ (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K := ⟨hx.1, hxe⟩
    rw [inf_centBar_eq_bot hQ hXN hK, Subgroup.mem_bot] at hx2
    rw [hx2]
    exact Subgroup.one_mem _
  have hzn : Subgroup.zpowers e ≤ Subgroup.normalizer ((Q ⊓ K : Subgroup G) : Set G) :=
    hcent'.trans (Subgroup.centralizer_le_normalizer _)
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hzn
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, orderOf_eq_prime he3 he1,
    card_inf_eq_27 hQ hQ1 hXN hKX hK] at hprod
  exact ⟨hel, by rw [hprod]⟩

end Structure

section Sup

variable {K Q X : Subgroup G}

theorem mem_sup_zpowers_of_pow_three (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hKe : ∀ x ∈ K, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    {y : G} (hy : y ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) (hy3 : y ^ 3 = 1) :
    y ∈ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := by
  classical
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (centBar 3 Q K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact commute_of_mem_centBar hQ hc ha
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcent hy
  have hac : Commute a c := (commute_of_mem_centBar hQ hc ha).symm
  have ha3 : a ^ 3 = 1 := (isElemAbelian_inf hQ hQ1 hXN hKX hK).2 a ha
  have hc3 : c ^ 3 = 1 := by
    rw [hac.mul_pow, ha3, one_mul] at hy3
    exact hy3
  have hce : c ∈ Subgroup.zpowers e :=
    mem_zpowers_of_pow_three_of_cyclic hcyc (e_mem_centBar hQ hXN hKe heQ) he3 he1 hc hc3
  exact Subgroup.mul_mem_sup ha hce

theorem eq_sup_zpowers_of_le (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hKe : ∀ x ∈ K, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    {F : Subgroup G} (hF : IsElemAbelian 3 F) (hF81 : Nat.card ↥F = 81)
    (hFle : F ≤ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) :
    F = (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := by
  have hsub : F ≤ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := by
    intro y hy
    exact mem_sup_zpowers_of_pow_three hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ (hFle hy)
      (hF.2 y hy)
  have hcard := (elemAbelian_sup_zpowers hQ hQ1 hXN hKX hK hKe he3 he1 heQ).2
  exact Subgroup.eq_of_le_of_card_ge hsub (by rw [hcard, hF81])

theorem card_le_81_of_elemAbelian (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3))
    (hC : Input113dCentralizer27) (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hKe : ∀ x ∈ K, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    {F : Subgroup G} (hFQ : F ≤ Q) (hF : IsElemAbelian 3 F) : Nat.card ↥F ≤ 81 := by
  by_contra hlt
  push Not at hlt
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hQp : IsPGroup 3 ↥Q := hQ.2.1
  have hU := Ubar_elemAbelian hQ hQ1 hXN hKX hK
  have hU27 := Ubar_card hQ hQ1 hXN hKX hK
  have hFle := le_sup_of_elemAbelian_card_ge hC e0 hQp hQK hcyc hU hU27 hFQ hF (by omega)
  have hsub : F ≤ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := by
    intro y hy
    exact mem_sup_zpowers_of_pow_three hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ (hFle hy)
      (hF.2 y hy)
  have hcard := (elemAbelian_sup_zpowers hQ hQ1 hXN hKX hK hKe he3 he1 heQ).2
  have := Subgroup.card_le_of_le hsub
  omega

end Sup

section Clause6

variable {K Q X E : Subgroup G}

theorem pRank_eq_four (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hC : Input113dCentralizer27)
    (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hKe : ∀ x ∈ K, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    (hEQ : E ≤ Q) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 4) :
    CFSG.Open.pRank 3 Q = 4 := by
  apply le_antisymm
  · obtain ⟨F, hFQ, hF, hFc⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) Q
    have hle := card_le_81_of_elemAbelian e0 hC hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ hFQ hF
    rw [hFc] at hle
    by_contra h
    push Not at h
    have h5 : 3 ^ 5 ≤ 3 ^ (CFSG.Open.pRank 3 Q) := Nat.pow_le_pow_right (by norm_num) h
    norm_num at h5 hle
    omega
  · exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEQ hEel hEcard

theorem thompsonJ_eq_E (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hC : Input113dCentralizer27)
    (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hKe : ∀ x ∈ K, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    (hEQ : E ≤ Q) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 4) :
    E = CFSG.LocalAnalysis.GLTheoremB.MovingAround.thompsonJ 3 Q := by
  have hp4 := pRank_eq_four e0 hC hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ hEQ hEel hEcard
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hU := Ubar_elemAbelian hQ hQ1 hXN hKX hK
  have hU27 := Ubar_card hQ hQ1 hXN hKX hK
  have hQp : IsPGroup 3 ↥Q := hQ.2.1
  have hEle : E ≤ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K :=
    le_sup_of_elemAbelian_card_ge hC e0 hQp hQK hcyc hU hU27 hEQ hEel (by rw [hEcard]; norm_num)
  have hEeq : E = (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e :=
    eq_sup_zpowers_of_le hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ hEel (by rw [hEcard]; norm_num) hEle
  unfold CFSG.LocalAnalysis.GLTheoremB.MovingAround.thompsonJ
  rw [hp4]
  apply le_antisymm
  · exact le_iSup₂ (f := fun (E' : Subgroup G) (_ : IsEkIn 3 4 Q E') => E') E
      ⟨hEQ, hEel, hEcard⟩
  · refine iSup₂_le fun F hF => ?_
    obtain ⟨hFQ, hFel, hFc⟩ := hF
    have hFc81 : Nat.card ↥F = 81 := by rw [hFc]; norm_num
    have hFle : F ≤ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K :=
      le_sup_of_elemAbelian_card_ge hC e0 hQp hQK hcyc hU hU27 hFQ hFel (by rw [hFc81])
    have hFeq := eq_sup_zpowers_of_le hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ hFel hFc81 hFle
    rw [hFeq, ← hEeq]
  
end Clause6

section Norm

theorem cube_eq_one_of_norm {C : Subgroup G} (hC : IsCyclic ↥C) (hC3 : IsPGroup 3 ↥C) {e t : G}
    (heC : e ∈ C) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (htC : ∀ c ∈ C, t * c * t⁻¹ ∈ C)
    (hte : t * e * t⁻¹ = e) {c : G} (hc : c ∈ C)
    (hN : c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹) = 1) : c ^ 3 = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥C)
  set γ : G := (g : G) with hγ
  have hγC : γ ∈ C := g.2
  have hCz : ∀ x ∈ C, ∃ k : ℤ, γ ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
    exact ⟨k, congrArg Subtype.val hk⟩
  have hCcard : Nat.card ↥C = orderOf γ := by
    have hz : C = Subgroup.zpowers γ := by
      ext x
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := hCz x hx
        exact Subgroup.mem_zpowers_iff.2 ⟨k, hk⟩
      · intro hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
        rw [← hk]
        exact C.zpow_mem hγC k
    rw [hz, Nat.card_zpowers]
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 3)).1 hC3
  have hNr : (orderOf γ : ℤ) = 3 ^ r := by
    have h : orderOf γ = 3 ^ r := hCcard.symm.trans hr
    exact_mod_cast h
  obtain ⟨α, hα⟩ := hCz (t * γ * t⁻¹) (htC γ hγC)
  have hφpow : ∀ k : ℤ, t * γ ^ k * t⁻¹ = γ ^ (α * k) := by
    intro k
    have h1 : (MulAut.conj t : G ≃* G) (γ ^ k) = ((MulAut.conj t : G ≃* G) γ) ^ k :=
      map_zpow _ _ _
    have h2 : ∀ x : G, t * x * t⁻¹ = (MulAut.conj t : G ≃* G) x := fun x => rfl
    rw [← h2, ← h2] at h1
    rw [h1, ← hα, ← zpow_mul]
  obtain ⟨j, hj⟩ := hCz c hc
  obtain ⟨m, hm⟩ := hCz e heC
  have hc1 : t * c * t⁻¹ = γ ^ (α * j) := by rw [← hj, hφpow]
  have hc2 : t ^ 2 * c * (t ^ 2)⁻¹ = γ ^ (α * (α * j)) := by
    have h : t ^ 2 * c * (t ^ 2)⁻¹ = t * (t * c * t⁻¹) * t⁻¹ := by
      simp only [sq, mul_inv_rev]
      group
    rw [h, hc1, hφpow]
  have hrel : γ ^ (j + α * j + α * (α * j)) = 1 := by
    rw [hc1, hc2, ← hj] at hN
    rw [← zpow_add, ← zpow_add] at hN
    exact hN
  have hdvd1 : (orderOf γ : ℤ) ∣ j + α * j + α * (α * j) :=
    orderOf_dvd_iff_zpow_eq_one.2 hrel
  have hem : γ ^ (α * m) = γ ^ m := by
    have h1 : t * e * t⁻¹ = γ ^ (α * m) := by rw [← hm, hφpow]
    rw [← h1, hte, ← hm]
  have hdvd_e : (orderOf γ : ℤ) ∣ α * m - m := by
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, hem, mul_inv_cancel]
  have hm_not : ¬ (orderOf γ : ℤ) ∣ m := by
    intro h
    apply he1
    rw [← hm]
    exact orderOf_dvd_iff_zpow_eq_one.1 h
  have h3α : (3 : ℤ) ∣ α - 1 := by
    by_contra hnd
    have hcop : IsCoprime (3 : ℤ) (α - 1) :=
      (Int.prime_three.irreducible.coprime_iff_not_dvd).2 hnd
    have hcop' : IsCoprime ((3 : ℤ) ^ r) (α - 1) := hcop.pow_left
    have hdiv : (3 : ℤ) ^ r ∣ m * (α - 1) := by
      have h' : m * (α - 1) = α * m - m := by ring
      rw [h', ← hNr]
      exact hdvd_e
    apply hm_not
    rw [hNr]
    exact hcop'.dvd_of_dvd_mul_right hdiv
  obtain ⟨s, hs⟩ := h3α
  have hα' : α = 1 + 3 * s := by linarith
  have hu : j + α * j + α * (α * j) = 3 * j * (1 + 3 * s + 3 * s ^ 2) := by
    rw [hα']
    ring
  have hnu : ¬ (3 : ℤ) ∣ (1 + 3 * s + 3 * s ^ 2) := by
    intro h
    have h' : (1 + 3 * s + 3 * s ^ 2 : ℤ) = 1 + 3 * (s + s ^ 2) := by ring
    rw [h'] at h
    have h1 : (3 : ℤ) ∣ 1 := (dvd_add_left (dvd_mul_right 3 _)).1 h
    norm_num at h1
  have hcop_u : IsCoprime ((3 : ℤ) ^ r) (1 + 3 * s + 3 * s ^ 2) :=
    ((Int.prime_three.irreducible.coprime_iff_not_dvd).2 hnu).pow_left
  have hdvd3 : (3 : ℤ) ^ r ∣ 3 * j * (1 + 3 * s + 3 * s ^ 2) := by
    rw [← hu, ← hNr]
    exact hdvd1
  have hdvd4 : (3 : ℤ) ^ r ∣ 3 * j := hcop_u.dvd_of_dvd_mul_right hdvd3
  have h3j : γ ^ (3 * j) = 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.1
    rw [hNr]
    exact hdvd4
  rw [← hj, ← zpow_natCast, ← zpow_mul]
  rw [show j * ((3 : ℕ) : ℤ) = 3 * j by push_cast; ring]
  exact h3j

end Norm

section Clause5

variable {K Q : Subgroup G}

theorem mem_normalizer_centBar {L : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (L : Set G))
    {q : G} (hq : q ∈ Q) : q ∈ Subgroup.normalizer ((centBar 3 Q L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact centBar_normal hQN hq hh
  · intro hh
    have := centBar_normal hQN (Q.inv_mem hq) hh
    have e : q⁻¹ * (q * h * q⁻¹) * q⁻¹⁻¹ = h := by group
    rw [e] at this
    exact this

theorem le_normalizer_sup_centBar {L : Subgroup G} (hQN : Q ≤ Subgroup.normalizer (L : Set G)) :
    Q ≤ Subgroup.normalizer (((Q ⊓ L : Subgroup G) ⊔ centBar 3 Q L : Subgroup G) : Set G) := by
  intro q hq
  exact mem_normalizer_sup (mem_normalizer_inf hq (hQN hq)) (mem_normalizer_centBar hQN hq)

theorem exists_eq_mul_zpow_of_sup_eq {N : Subgroup G} {x : G} (hNQ : N ≤ Q)
    (hNn : ∀ q ∈ Q, ∀ n ∈ N, q * n * q⁻¹ ∈ N) (hxQ : x ∈ Q) (hT : N ⊔ Subgroup.zpowers x = Q)
    {y : G} (hy : y ∈ Q) : ∃ n ∈ N, ∃ k : ℤ, y = n * x ^ k := by
  classical
  haveI : (N.subgroupOf Q).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.2 (hNn g g.2 n (Subgroup.mem_subgroupOf.1 hn))⟩
  have htop : N.subgroupOf Q ⊔ (Subgroup.zpowers x).subgroupOf Q = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNQ (Subgroup.zpowers_le.2 hxQ), hT, Subgroup.subgroupOf_self]
  have hz : (⟨y, hy⟩ : ↥Q) ∈ N.subgroupOf Q ⊔ (Subgroup.zpowers x).subgroupOf Q := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨n', hn', h', hh', hprod⟩ := Subgroup.mem_sup_of_normal_left.1 hz
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hh')
  refine ⟨(n' : G), Subgroup.mem_subgroupOf.1 hn', k, ?_⟩
  have h1 : ((n' * h' : ↥Q) : G) = y := congrArg Subtype.val hprod
  rw [← h1]
  show (n' : G) * (h' : G) = (n' : G) * x ^ k
  rw [hk]

theorem sup_zpowers_eq_top (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hcard_Q : Nat.card ↥Q ≤ 81 * Nat.card ↥(centBar 3 Q K))
    (hK0 : Nat.card ↥(Q ⊓ K : Subgroup G) = 27)
    (hcomm : ∀ a ∈ (Q ⊓ K : Subgroup G), ∀ c ∈ centBar 3 Q K, a * c = c * a)
    (hinf : (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K = ⊥)
    {x : G} (hxQ : x ∈ Q) (hx3 : x ^ 3 = 1)
    (hxN : x ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) :
    ((Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) ⊔ Subgroup.zpowers x = Q := by
  classical
  set N : Subgroup G := (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K with hNdef
  have hNQ : N ≤ Q := sup_le inf_le_left (fun c hc => (mem_centBar_iff.1 hc).1)
  have hQN' : Q ≤ Subgroup.normalizer (N : Set G) := le_normalizer_sup_centBar hQK
  have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (N : Set G) :=
    Subgroup.zpowers_le.2 (hQN' hxQ)
  have hcn : (centBar 3 Q K : Subgroup G) ≤ Subgroup.normalizer ((Q ⊓ K : Subgroup G) : Set G) := by
    intro c hc
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcomm a ha c hc)
  have hprodN := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hcn
  rw [hinf, Subgroup.card_bot, mul_one, hK0] at hprodN
  have hx1 : x ≠ 1 := fun h => hxN (h ▸ N.one_mem)
  have hxord : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hinter : Nat.card ↥(N ⊓ Subgroup.zpowers x) = 1 := by
    have hdvd : Nat.card ↥(N ⊓ Subgroup.zpowers x) ∣ 3 := by
      rw [← hxord]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h | h
    · exact h
    · exfalso
      have heq : N ⊓ Subgroup.zpowers x = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h, hxord])
      have hxmem : x ∈ N ⊓ Subgroup.zpowers x := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxN hxmem.1
  have hprodx := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hzN
  rw [hinter, mul_one, hxord] at hprodx
  have hle : N ⊔ Subgroup.zpowers x ≤ Q := sup_le hNQ (Subgroup.zpowers_le.2 hxQ)
  have hcardQ : Nat.card ↥Q ≤ Nat.card ↥(N ⊔ Subgroup.zpowers x) := by
    have h81 : Nat.card ↥(N ⊔ Subgroup.zpowers x) = 81 * Nat.card ↥(centBar 3 Q K) := by
      rw [hprodx]
      have : Nat.card ↥N = 27 * Nat.card ↥(centBar 3 Q K) := by
        rw [← hprodN]
      rw [this]
      ring
    rw [h81]
    exact hcard_Q
  exact Subgroup.eq_of_le_of_card_ge hle hcardQ


theorem c_mem_zpowers_of_norm {X : Subgroup G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hXe : ∀ x ∈ X, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    {a c t : G} (ha : a ∈ (Q ⊓ K : Subgroup G)) (hc : c ∈ centBar 3 Q K) (htQ : t ∈ Q)
    (ht3 : t ^ 3 = 1) (hy : (a * c * t) ^ 3 = 1) : c ∈ Subgroup.zpowers e := by
  classical
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hQp : IsPGroup 3 ↥Q := hQ.2.1
  have hKe : ∀ x ∈ K, e * x = x * e := fun x hx => hXe x (hKX hx)
  have hnormK : ∀ q ∈ Q, ∀ n ∈ (Q ⊓ K : Subgroup G), q * n * q⁻¹ ∈ (Q ⊓ K : Subgroup G) :=
    fun q hq n hn => (Subgroup.mem_normalizer_iff.1 (mem_normalizer_inf hq (hQK hq)) n).1 hn
  have hcentQ : ∀ q ∈ Q, ∀ u ∈ centBar 3 Q K, q * u * q⁻¹ ∈ centBar 3 Q K :=
    fun q hq u hu => centBar_normal hQK hq hu
  have htQ2 : t ^ 2 ∈ Q := Q.pow_mem htQ 2
  have ha1 : t * a * t⁻¹ ∈ (Q ⊓ K : Subgroup G) := hnormK t htQ a ha
  have ha2 : t ^ 2 * a * (t ^ 2)⁻¹ ∈ (Q ⊓ K : Subgroup G) := hnormK _ htQ2 a ha
  have hc1 : t * c * t⁻¹ ∈ centBar 3 Q K := hcentQ t htQ c hc
  have hc2 : t ^ 2 * c * (t ^ 2)⁻¹ ∈ centBar 3 Q K := hcentQ _ htQ2 c hc
  have hca1 : c * (t * a * t⁻¹) = (t * a * t⁻¹) * c := commute_of_mem_centBar hQ hc ha1
  have hca2 : c * (t ^ 2 * a * (t ^ 2)⁻¹) = (t ^ 2 * a * (t ^ 2)⁻¹) * c :=
    commute_of_mem_centBar hQ hc ha2
  have hc1a2 : (t * c * t⁻¹) * (t ^ 2 * a * (t ^ 2)⁻¹) = (t ^ 2 * a * (t ^ 2)⁻¹) * (t * c * t⁻¹) :=
    commute_of_mem_centBar hQ hc1 ha2
  have hprod0 : a * c * (t * (a * c) * t⁻¹) * (t ^ 2 * (a * c) * (t ^ 2)⁻¹) = 1 := by
    have h1 : (a * c * t) ^ 3 = a * c * (t * (a * c) * t⁻¹) * (t ^ 2 * (a * c) * (t ^ 2)⁻¹) *
        t ^ 3 := by
      simp only [pow_three, pow_two, mul_inv_rev]
      group
    rw [h1, ht3, mul_one] at hy
    exact hy
  have e1 : t * (a * c) * t⁻¹ = (t * a * t⁻¹) * (t * c * t⁻¹) := by group
  have e2 : t ^ 2 * (a * c) * (t ^ 2)⁻¹ = (t ^ 2 * a * (t ^ 2)⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹) := by
    simp only [pow_two, mul_inv_rev]
    group
  rw [e1, e2] at hprod0
  have key : (a * (t * a * t⁻¹) * (t ^ 2 * a * (t ^ 2)⁻¹)) *
      (c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹)) = 1 := by
    have hX : a * (t * a * t⁻¹) * (t ^ 2 * a * (t ^ 2)⁻¹) *
        (c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹)) =
        a * c * ((t * a * t⁻¹) * (t * c * t⁻¹)) * ((t ^ 2 * a * (t ^ 2)⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹)) := by
      calc a * (t * a * t⁻¹) * (t ^ 2 * a * (t ^ 2)⁻¹) *
            (c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹))
          = a * (t * a * t⁻¹) * ((t ^ 2 * a * (t ^ 2)⁻¹) * c) * (t * c * t⁻¹) *
              (t ^ 2 * c * (t ^ 2)⁻¹) := by simp only [mul_assoc]
        _ = a * (t * a * t⁻¹) * (c * (t ^ 2 * a * (t ^ 2)⁻¹)) * (t * c * t⁻¹) *
              (t ^ 2 * c * (t ^ 2)⁻¹) := by rw [← hca2]
        _ = a * ((t * a * t⁻¹) * c) * (t ^ 2 * a * (t ^ 2)⁻¹) * (t * c * t⁻¹) *
              (t ^ 2 * c * (t ^ 2)⁻¹) := by simp only [mul_assoc]
        _ = a * (c * (t * a * t⁻¹)) * (t ^ 2 * a * (t ^ 2)⁻¹) * (t * c * t⁻¹) *
              (t ^ 2 * c * (t ^ 2)⁻¹) := by rw [← hca1]
        _ = a * c * (t * a * t⁻¹) * ((t ^ 2 * a * (t ^ 2)⁻¹) * (t * c * t⁻¹)) *
              (t ^ 2 * c * (t ^ 2)⁻¹) := by simp only [mul_assoc]
        _ = a * c * (t * a * t⁻¹) * ((t * c * t⁻¹) * (t ^ 2 * a * (t ^ 2)⁻¹)) *
              (t ^ 2 * c * (t ^ 2)⁻¹) := by rw [← hc1a2]
        _ = a * c * ((t * a * t⁻¹) * (t * c * t⁻¹)) * ((t ^ 2 * a * (t ^ 2)⁻¹) *
              (t ^ 2 * c * (t ^ 2)⁻¹)) := by simp only [mul_assoc]
    rw [hX]
    exact hprod0
  have hmem1 : c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹) ∈ (Q ⊓ K : Subgroup G) := by
    have hinv := eq_inv_of_mul_eq_one_right key
    rw [hinv]
    exact (Q ⊓ K).inv_mem (mul_mem (mul_mem ha ha1) ha2)
  have hmem2 : c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹) ∈ centBar 3 Q K :=
    mul_mem (mul_mem hc hc1) hc2
  have hone : c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹) = 1 := by
    have hI : c * (t * c * t⁻¹) * (t ^ 2 * c * (t ^ 2)⁻¹) ∈ (Q ⊓ K : Subgroup G) ⊓ centBar 3 Q K :=
      ⟨hmem1, hmem2⟩
    rw [inf_centBar_eq_bot hQ hXN hK, Subgroup.mem_bot] at hI
    exact hI
  have hcyc3 : IsPGroup 3 ↥(centBar 3 Q K) := hQp.to_le (fun c' hc' => (mem_centBar_iff.1 hc').1)
  have hte : t * e * t⁻¹ = e := by
    rw [← hXe t (hQ.1 htQ)]
    group
  have hc3 : c ^ 3 = 1 :=
    cube_eq_one_of_norm hcyc hcyc3 (e_mem_centBar hQ hXN hKe heQ) he3 he1
      (fun c' hc' => hcentQ t htQ c' hc') hte hc hone
  exact mem_zpowers_of_pow_three_of_cyclic hcyc (e_mem_centBar hQ hXN hKe heQ) he3 he1 hc hc3

theorem exists_mem_not_mem_sup {X A : Subgroup G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hKe : ∀ x ∈ K, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    (hAmax : ∀ F : Subgroup G, F ≤ ⊤ → IsElemAbelian 3 F → A ≤ F → F = A)
    (hAel : IsElemAbelian 3 A) (hAcard : Nat.card ↥A = 27) :
    ∃ x ∈ A, x ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := by
  by_contra h
  push Not at h
  have hAE : A ≤ (Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e := by
    intro a ha
    exact mem_sup_zpowers_of_pow_three hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ (h a ha)
      (hAel.2 a ha)
  have hE' := elemAbelian_sup_zpowers hQ hQ1 hXN hKX hK hKe he3 he1 heQ
  have hEq := hAmax _ le_top hE'.1 hAE
  have h1 : Nat.card ↥A = Nat.card ↥((Q ⊓ K : Subgroup G) ⊔ Subgroup.zpowers e) := by
    rw [hEq]
  rw [hE'.2, hAcard] at h1
  norm_num at h1

theorem omegaOne_eq_of (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3)) (hC : Input113dCentralizer27)
    {X : Subgroup G} (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    {e : G} (hXe : ∀ x ∈ X, e * x = x * e) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    {E A : Subgroup G} (hEQ : E ≤ Q) (hEel : IsElemAbelian 3 E) (hEcard : Nat.card ↥E = 3 ^ 4)
    (hAQ : A ≤ Q) (hAel : IsElemAbelian 3 A) (hAcard : Nat.card ↥A = 3 ^ 3)
    (hAmax : ∀ F : Subgroup G, F ≤ ⊤ → IsElemAbelian 3 F → A ≤ F → F = A) :
    omegaOne 3 Q = E ⊔ A := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKe : ∀ x ∈ K, e * x = x * e := fun x hx => hXe x (hKX hx)
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hQp : IsPGroup 3 ↥Q := hQ.2.1
  have hU := Ubar_elemAbelian hQ hQ1 hXN hKX hK
  have hU27 := Ubar_card hQ hQ1 hXN hKX hK
  have hEle := le_sup_of_elemAbelian_card_ge hC e0 hQp hQK hcyc hU hU27 hEQ hEel
    (by rw [hEcard]; norm_num)
  have hEeq := eq_sup_zpowers_of_le hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ hEel
    (by rw [hEcard]; norm_num) hEle
  have hAcard' : Nat.card ↥A = 27 := by rw [hAcard]; norm_num
  obtain ⟨x, hxA, hxN⟩ := exists_mem_not_mem_sup hQ hQ1 hXN hKX hK hcyc hKe he3 he1 heQ
    hAmax hAel hAcard'
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hxQ : x ∈ Q := hAQ hxA
  have hcomm : ∀ a ∈ (Q ⊓ K : Subgroup G), ∀ c ∈ centBar 3 Q K, a * c = c * a :=
    fun a ha c hc => (commute_of_mem_centBar hQ hc ha).symm
  have hinf := inf_centBar_eq_bot hQ hXN hK
  have hcard_Q := card_le_81_mul_centBar e0 hQp hQK
  have hT := sup_zpowers_eq_top hQK hcard_Q (card_inf_eq_27 hQ hQ1 hXN hKX hK) hcomm hinf hxQ
    hx3 hxN
  have hNQ : (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K ≤ Q :=
    sup_le inf_le_left (fun c hc => (mem_centBar_iff.1 hc).1)
  have hNn : ∀ q ∈ Q, ∀ n ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K,
      q * n * q⁻¹ ∈ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K := fun q hq n hn =>
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_sup_centBar hQK hq) n).1 hn
  have hcent : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer (centBar 3 Q K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (hcomm a ha c hc).symm
  have hC3 : IsPGroup 3 ↥(centBar 3 Q K) := hQp.to_le (fun c hc => (mem_centBar_iff.1 hc).1)
  unfold omegaOne
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyQ, hy3⟩
    obtain ⟨n, hn, k, rfl⟩ := exists_eq_mul_zpow_of_sup_eq hNQ hNn hxQ hT hyQ
    obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcent hn
    have htQ : x ^ k ∈ Q := Q.zpow_mem hxQ k
    have ht3 : (x ^ k) ^ 3 = 1 := by
      have h' : (x ^ k) ^ 3 = (x ^ 3) ^ k := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      rw [h', hx3, one_zpow]
    have hcz : c ∈ Subgroup.zpowers e :=
      c_mem_zpowers_of_norm hQ hQ1 hXN hKX hK hcyc hXe he3 he1 heQ ha hc htQ ht3 hy3
    have hn' : a * c ∈ E := by
      rw [hEeq]
      exact Subgroup.mul_mem_sup ha hcz
    exact Subgroup.mul_mem_sup hn' (A.zpow_mem hxA k)
  · apply sup_le
    · intro y hy
      exact Subgroup.subset_closure ⟨hEQ hy, hEel.2 y hy⟩
    · intro y hy
      exact Subgroup.subset_closure ⟨hAQ hy, hAel.2 y hy⟩

end Clause5

section Clause7a

theorem conj_eq_zpow_of_mem_normalizer {n e : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G)) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    ∃ k : ℤ, ¬ (3 : ℤ) ∣ k ∧ n * e * n⁻¹ = e ^ k := by
  have he3z : e ^ (3 : ℤ) = 1 := by simpa using he3
  have hmem : n * e * n⁻¹ ∈ Subgroup.zpowers e :=
    (Subgroup.mem_normalizer_iff.1 hn e).1 (Subgroup.mem_zpowers e)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine ⟨k, ?_, hk.symm⟩
  rintro ⟨m, rfl⟩
  apply he1
  have h1 : n * e * n⁻¹ = 1 := by
    rw [← hk, zpow_mul, he3z, one_zpow]
  calc e = n⁻¹ * (n * e * n⁻¹) * n := by group
    _ = n⁻¹ * 1 * n := by rw [h1]
    _ = 1 := by group

theorem commute_zpow_iff_of_three_not_dvd {y e : G} (he3 : e ^ 3 = 1) {k : ℤ}
    (hk : ¬ (3 : ℤ) ∣ k) : Commute y (e ^ k) ↔ Commute y e := by
  obtain ⟨u, v, huv⟩ : IsCoprime (3 : ℤ) k :=
    (Int.prime_three.irreducible.coprime_iff_not_dvd).2 hk
  have he3z : e ^ (3 : ℤ) = 1 := by simpa using he3
  have hek : e = (e ^ k) ^ v := by
    calc e = e ^ (3 * u + k * v) := by
          rw [show 3 * u + k * v = u * 3 + v * k by ring, huv, zpow_one]
      _ = (e ^ (3 : ℤ)) ^ u * (e ^ k) ^ v := by rw [zpow_add, zpow_mul, zpow_mul]
      _ = (e ^ k) ^ v := by rw [he3z, one_zpow, one_mul]
  constructor
  · intro h
    rw [hek]
    exact h.zpow_right v
  · intro h
    exact h.zpow_right k

theorem commute_conj_iff (n a b : G) :
    Commute (n * a * n⁻¹) (n * b * n⁻¹) ↔ Commute a b := by
  constructor
  · intro h
    have e1 : ∀ x : G, (MulAut.conj n⁻¹ : G ≃* G) (n * x * n⁻¹) = x := fun x => by
      show n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x
      group
    have h' := h.map (MulAut.conj n⁻¹ : G ≃* G)
    rwa [e1, e1] at h'
  · intro h
    exact h.map (MulAut.conj n : G ≃* G)

theorem gLBConj_centralizer_eq {n e : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G)) (he3 : e ^ 3 = 1) (he1 : e ≠ 1) :
    GLBConj n (Subgroup.centralizer ({e} : Set G)) = Subgroup.centralizer ({e} : Set G) := by
  obtain ⟨k, hk, hnk⟩ := conj_eq_zpow_of_mem_normalizer hn he3 he1
  ext y
  rw [mem_gLBConj, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  have key : Commute (n * y * n⁻¹) e ↔ Commute y e := by
    rw [← commute_zpow_iff_of_three_not_dvd he3 hk, ← hnk, commute_conj_iff]
  exact Commute.symm_iff.trans (key.trans Commute.symm_iff)


theorem zmod3_pow_three_pow (k : ℤ) (j : ℕ) : ((k ^ (3 ^ j) : ℤ) : ZMod 3) = (k : ZMod 3) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hcube : ∀ x : ZMod 3, x ^ 3 = x := by decide
    rw [pow_succ, pow_mul, Int.cast_pow, ih]
    exact hcube _

theorem commute_of_three_power_mem_normalizer {n e : G}
    (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G)) (he3 : e ^ 3 = 1) (he1 : e ≠ 1)
    {j : ℕ} (hj : n ^ (3 ^ j) = 1) : Commute n e := by
  obtain ⟨k, hk, hnk⟩ := conj_eq_zpow_of_mem_normalizer hn he3 he1
  have hpow : ∀ m : ℕ, n ^ m * e * (n ^ m)⁻¹ = e ^ (k ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 : n ^ (m + 1) * e * (n ^ (m + 1))⁻¹ = n * (n ^ m * e * (n ^ m)⁻¹) * n⁻¹ := by
        rw [pow_succ']
        group
      rw [h1, ih]
      have h2 : n * e ^ (k ^ m) * n⁻¹ = (n * e * n⁻¹) ^ (k ^ m) := by
        have h3 := map_zpow (MulAut.conj n : G ≃* G) e (k ^ m)
        simp only [MulAut.conj_apply] at h3
        exact h3
      rw [h2, hnk, ← zpow_mul, pow_succ, mul_comm (k ^ m) k]
  have hfix : e ^ (k ^ (3 ^ j)) = e := by
    rw [← hpow, hj]
    group
  have he3z : e ^ (3 : ℤ) = 1 := by simpa using he3
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hdvd : (orderOf e : ℤ) ∣ k ^ (3 ^ j) - 1 := by
    apply orderOf_dvd_iff_zpow_eq_one.2
    rw [zpow_sub, zpow_one, hfix, mul_inv_cancel]
  rw [hord] at hdvd
  have hz : ((k ^ (3 ^ j) - 1 : ℤ) : ZMod 3) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hdvd
  rw [Int.cast_sub, Int.cast_one, sub_eq_zero, zmod3_pow_three_pow] at hz
  have hk1 : ((3 : ℕ) : ℤ) ∣ k - 1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (k - 1) 3).1 (by rw [Int.cast_sub, Int.cast_one, hz, sub_self])
  rw [← hord] at hk1
  have hek : e ^ k = e := by
    have h1 : e ^ (k - 1) = 1 := orderOf_dvd_iff_zpow_eq_one.1 hk1
    calc e ^ k = e ^ (k - 1 + 1) := by rw [sub_add_cancel]
      _ = e ^ (k - 1) * e := zpow_add_one e (k - 1)
      _ = e := by rw [h1, one_mul]
  have hcomm : n * e * n⁻¹ = e := by rw [hnk, hek]
  show n * e = e * n
  calc n * e = (n * e * n⁻¹) * n := by group
    _ = e * n := by rw [hcomm]

theorem isSylowIn_normalizer_zpowers {X Q : Subgroup G} {e : G}
    (hX : X = Subgroup.centralizer ({e} : Set G)) (hQ : IsSylowIn 3 X Q) (he3 : e ^ 3 = 1)
    (he1 : e ≠ 1) :
    IsSylowIn 3 (Subgroup.normalizer (Subgroup.zpowers e : Set G)) Q := by
  have hXc : X ≤ Subgroup.centralizer (Subgroup.zpowers e : Set G) := by
    intro x hx
    rw [hX] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hxe : Commute x e := (Subgroup.mem_centralizer_iff.1 hx e (Set.mem_singleton e)).symm
    exact (hxe.zpow_right m).eq.symm
  have hXN : X ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
    hXc.trans (Subgroup.centralizer_le_normalizer _)
  refine ⟨hQ.1.trans hXN, hQ.2.1, fun R' hR'N hR'p hQR' => ?_⟩
  have hR'X : R' ≤ X := by
    intro r hr
    rw [hX]
    rw [← hX]
    have hpow : ∃ k : ℕ, r ^ (3 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hR'p ⟨r, hr⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    obtain ⟨k, hk⟩ := hpow
    have hcomm := commute_of_three_power_mem_normalizer (hR'N hr) he3 he1 hk
    rw [hX]
    exact Subgroup.mem_centralizer_iff.2 (fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact hcomm.eq.symm)
  exact hQ.2.2 R' hR'X hR'p hQR'


section TwoComp

theorem mk_mem_barX {X K : Subgroup G} (hKX : K ≤ X) {q : G} (hq : q ∈ K) :
    (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨q, hKX hq⟩ : ↥X)) ∈ barX 3 X K :=
  Subgroup.mem_map.2 ⟨⟨q, hKX hq⟩, Subgroup.mem_subgroupOf.2 hq, rfl⟩

theorem comm_and_inf_of_two_components {X K K' Q : Subgroup G} (hQ : IsSylowIn 3 X Q)
    (hK : GLAPComponent 3 X K) (hK' : GLAPComponent 3 X K') (hne : K ≠ K')
    (hKX : K ≤ X) (hK'X : K' ≤ X) (hKI' : IsLTwoTwentySeven (barOf 3 K')) :
    (∀ q ∈ (Q ⊓ K : Subgroup G), ∀ q' ∈ (Q ⊓ K' : Subgroup G), q * q' = q' * q) ∧
      (Q ⊓ K : Subgroup G) ⊓ (Q ⊓ K' : Subgroup G) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 ↥(Q.subgroupOf X) :=
    hQ.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hQ.1).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQ.1).injective
  have hcore : ∀ w : ↥X, w ∈ GLAPPrimeCore 3 ↥X → ((w : ↥X) : G) ∈ Q → w = 1 := by
    intro w hwO hwQ
    have hmem : w ∈ GLAPPrimeCore 3 ↥X ⊓ (Q.subgroupOf X) :=
      ⟨hwO, Subgroup.mem_subgroupOf.2 hwQ⟩
    rw [Lemma113c.core_inf_eq_bot hQp, Subgroup.mem_bot] at hmem
    exact hmem
  constructor
  · intro q hq q' hq'
    have hqK : q ∈ K := (Subgroup.mem_inf.1 hq).2
    have hqX : q ∈ X := hKX hqK
    have hqQ : q ∈ Q := (Subgroup.mem_inf.1 hq).1
    have hq'K : q' ∈ K' := (Subgroup.mem_inf.1 hq').2
    have hq'X : q' ∈ X := hK'X hq'K
    have hq'Q : q' ∈ Q := (Subgroup.mem_inf.1 hq').1
    have hcomm := Lemma113c.barX_comm_of_ne hK hK' hne _ (mk_mem_barX hKX hqK) _
      (mk_mem_barX hK'X hq'K)
    have hmk : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X)
        ((⟨q, hqX⟩ : ↥X) * ⟨q', hq'X⟩) =
        QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) ((⟨q', hq'X⟩ : ↥X) * ⟨q, hqX⟩) := by
      rw [map_mul, map_mul]
      exact hcomm
    have hw := mul_inv_mem_of_mk_eq (N := GLAPPrimeCore 3 ↥X) hmk
    have hwQ : ((((⟨q, hqX⟩ : ↥X) * ⟨q', hq'X⟩) * ((⟨q', hq'X⟩ : ↥X) * ⟨q, hqX⟩)⁻¹ : ↥X) : G) ∈
        Q := by
      exact Q.mul_mem (Q.mul_mem hqQ hq'Q) (Q.inv_mem (Q.mul_mem hq'Q hqQ))
    have h1 := hcore _ hw hwQ
    have h2 := mul_inv_eq_one.1 h1
    exact congrArg Subtype.val h2
  · apply eq_bot_iff.2
    rintro z ⟨hzQK, hzK'⟩
    have hzK : z ∈ K := (Subgroup.mem_inf.1 hzQK).2
    have hzQ : z ∈ Q := (Subgroup.mem_inf.1 hzQK).1
    have hzK'Q : z ∈ K' := (Subgroup.mem_inf.1 hzK').2
    have hzX : z ∈ X := hKX hzK
    obtain ⟨eI⟩ := barX_isLTwoTwentySeven hK' hKI'
    have hmemI : QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨z, hzX⟩ : ↥X) ∈ barX 3 X K' :=
      mk_mem_barX hK'X hzK'Q
    have hcentral : ∀ s : ↥(barX 3 X K'), s * (⟨_, hmemI⟩ : ↥(barX 3 X K')) =
        (⟨_, hmemI⟩ : ↥(barX 3 X K')) * s := by
      intro s
      have h := Lemma113c.barX_comm_of_ne hK hK' hne _ (mk_mem_barX hKX hzK) _ s.2
      exact Subtype.ext h.symm
    have hone := Lemma113c.psl2_27_centre eI _ hcentral
    have hO : (QuotientGroup.mk' (GLAPPrimeCore 3 ↥X) (⟨z, hzX⟩ : ↥X)) = 1 :=
      congrArg Subtype.val hone
    have hzO : (⟨z, hzX⟩ : ↥X) ∈ GLAPPrimeCore 3 ↥X := (QuotientGroup.eq_one_iff _).1 hO
    have hz1 := hcore _ hzO hzQ
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hz1


theorem normalizer_zpowers_le_normalizer_K {X K Q M : Subgroup G} {e a : G}
    (hX : X = Subgroup.centralizer ({e} : Set G)) (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥)
    (hXN : X ≤ Subgroup.normalizer (K : Set G)) (hKX : K ≤ X)
    (hK : GLAPComponent 3 X K) (hKI : IsLTwoTwentySeven (barOf 3 K))
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (hQM : Q ≤ M) (ha : a ∈ Q)
    (h0 : ∀ E1 : Subgroup G, E1 ≤ M → IsElemAbelian 3 E1 → 5 ≤ CFSG.Open.pRank 3 E1 →
      a ∉ Subgroup.normalizer (E1 : Set G)) :
    Subgroup.normalizer (Subgroup.zpowers e : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro n hn
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hnX : GLBConj n X = X := by
    rw [hX]
    exact gLBConj_centralizer_eq hn he3 he1
  have hK'comp : GLAPComponent 3 X (GLBConj n K) := by
    have h := CFSG.HardMathSupport.Solomon.LocalBalance.glaPComponent_gLBConj n hK
    rw [hnX] at h
    exact h
  have hK'X : GLBConj n K ≤ X := by
    have h := gLBConj_mono n hKX
    rw [hnX] at h
    exact h
  have hKI' : IsLTwoTwentySeven (barOf 3 (GLBConj n K)) := by
    obtain ⟨e0⟩ := hKI
    exact ⟨(CFSG.LocalAnalysis.GLTheoremB.conjQuotEquiv 3 n K).symm.trans e0⟩
  have hXK' : X ≤ Subgroup.normalizer ((GLBConj n K : Subgroup G) : Set G) := by
    intro x hx
    rw [mem_normalizer_iff_gLBConj_eq]
    have hx' : n * x * n⁻¹ ∈ X := by
      have hmem : x ∈ GLBConj n X := by
        rw [hnX]
        exact hx
      exact mem_gLBConj.1 hmem
    have hK_eq : GLBConj (n * x * n⁻¹) K = K := mem_normalizer_iff_gLBConj_eq.1 (hXN hx')
    rw [gLBConj_gLBConj]
    have hnx : n * x = (n * x * n⁻¹) * n := by group
    rw [hnx, ← gLBConj_gLBConj, hK_eq]
  by_contra hnK
  have hne : GLBConj n K ≠ K := fun h => hnK (mem_normalizer_iff_gLBConj_eq.2 h)
  obtain ⟨hcomm, hinf⟩ := comm_and_inf_of_two_components hQ hK hK'comp (Ne.symm hne) hKX hK'X
    hKI'
  have hQ0 : IsElemAbelian 3 (Q ⊓ K : Subgroup G) := isElemAbelian_inf hQ hQ1 hXN hKX hKI
  have hQ0' : IsElemAbelian 3 (Q ⊓ GLBConj n K : Subgroup G) :=
    isElemAbelian_inf hQ hQ1 hXK' hK'X hKI'
  have hcommE : (Q ⊓ K : Subgroup G) ≤ Subgroup.centralizer ((Q ⊓ GLBConj n K : Subgroup G) : Set G) :=
    fun q hq => Subgroup.mem_centralizer_iff.2 (fun q' hq' => (hcomm q hq q' hq').symm)
  have hE1el : IsElemAbelian 3 ((Q ⊓ K : Subgroup G) ⊔ (Q ⊓ GLBConj n K : Subgroup G)) :=
    isElemAbelian_sup_of_commute hQ0 hQ0' hcommE
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hcommE.trans (Subgroup.centralizer_le_normalizer _))
  rw [inf_comm (Q ⊓ GLBConj n K : Subgroup G) (Q ⊓ K : Subgroup G), hinf, Subgroup.card_bot,
    mul_one, card_inf_eq_27 hQ hQ1 hXN hKX hKI, card_inf_eq_27 hQ hQ1 hXK' hK'X hKI'] at hprod
  have hE1card : Nat.card ↥((Q ⊓ K : Subgroup G) ⊔ (Q ⊓ GLBConj n K : Subgroup G)) = 3 ^ 6 := by
    rw [sup_comm, hprod]
    norm_num
  have hE1Q : (Q ⊓ K : Subgroup G) ⊔ (Q ⊓ GLBConj n K : Subgroup G) ≤ Q :=
    sup_le inf_le_left inf_le_left
  have hE1M : (Q ⊓ K : Subgroup G) ⊔ (Q ⊓ GLBConj n K : Subgroup G) ≤ M := hE1Q.trans hQM
  have hE1n : Q ≤ Subgroup.normalizer (((Q ⊓ K : Subgroup G) ⊔ (Q ⊓ GLBConj n K : Subgroup G) :
      Subgroup G) : Set G) := fun q hq =>
    mem_normalizer_sup (mem_normalizer_inf hq (hQK hq)) (mem_normalizer_inf hq (hXK' (hQ.1 hq)))
  have h6 := l113_pRank_eq hE1el hE1card
  exact h0 _ hE1M hE1el (by rw [h6]; norm_num) (hE1n ha)

end TwoComp
end Clause7a

section Clause7b

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (semilinearEquivAut)

@[expose] noncomputable def galHom {Y : Type} [Group Y] (e0 : Y ≃* PSL2 (GaloisField 3 3)) :
    MulAut Y →* (GaloisField 3 3 ≃+* GaloisField 3 3) :=
  (SemidirectProduct.rightHom.comp (semilinearEquivAut (GaloisField 3 3)).symm.toMonoidHom).comp
    (MulAut.congr e0).toMonoidHom

theorem finite_ringAut_card : Nat.card (GaloisField 3 3 ≃+* GaloisField 3 3) = 3 :=
  CFSG.RankThree.PartTwo.KFacts.card_ringAut_galoisField_three_three

theorem hom_kills_three_prime {N T : Type} [Group N] [Group T] [Finite T] (hT : Nat.card T = 3)
    (φ : N →* T) {g : N} (hg : ¬ (3 : ℕ) ∣ orderOf g) : φ g = 1 := by
  have h1 : orderOf (φ g) ∣ orderOf g := orderOf_map_dvd φ g
  have h2 : orderOf (φ g) ∣ 3 := by
    have := orderOf_dvd_natCard (φ g)
    rwa [hT] at this
  have h3 : orderOf (φ g) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 h2 with h | h
    · exact h
    · exfalso
      apply hg
      rw [← h]
      exact h1
  exact orderOf_eq_one_iff.1 h3

theorem galHom_rho_ne_one {K Q : Subgroup G} {x : G} (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3))
    (hQp : IsPGroup 3 ↥Q) (hQK : Q ≤ Subgroup.normalizer (K : Set G))
    (hU27 : Nat.card ↥(Ubar hQK) = 27)
    (hxQ : x ∈ Q) (hx3 : x ^ 3 = 1) (hxN : x ∉ (Q ⊓ K : Subgroup G) ⊔ centBar 3 Q K) :
    galHom e0 (barAut 3 K ⟨x, hQK hxQ⟩) ≠ 1 := by
  intro h
  have hρ3 : (barAut 3 K ⟨x, hQK hxQ⟩) ^ 3 = 1 := by
    have h1 : (⟨x, hQK hxQ⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hx3)
    rw [← map_pow, h1, map_one]
  have hα3 : (MulAut.congr e0 (barAut 3 K ⟨x, hQK hxQ⟩)) ^ 3 = 1 := by
    rw [← map_pow, hρ3, map_one]
  have h' : SemidirectProduct.rightHom
      ((semilinearEquivAut (GaloisField 3 3)).symm (MulAut.congr e0 (barAut 3 K ⟨x, hQK hxQ⟩))) = 1 :=
    h
  have hmem := CFSG.RankThree.PartTwo.KFacts.mem_range_pglAction_of_rightHom_eq_one h'
  have hinner := CFSG.RankThree.PartTwo.KFacts.isInnerAut_of_mem_inndiag_of_pow_three hmem hα3
  have hinner' : CFSG.RankThree.PartTwo.KFacts.IsInnerAut (barAut 3 K ⟨x, hQK hxQ⟩) :=
    (CFSG.RankThree.PartTwo.KFacts.isInnerAut_congr e0 _).1 hinner
  exact hxN (mem_sup_of_rho_inner e0 hQp hQK hU27 ⟨x, hxQ⟩ hinner')

end Clause7b

section Clause7c

@[expose] def Input113dGrun : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (Q : Subgroup G), IsSimpleGroup G → orderOf z = 3 →
    IsSylowIn 3 (Subgroup.normalizer (Subgroup.zpowers z : Set G)) Q →
    (∀ q ∈ Q, q * z = z * q) →
    (∀ g : G, GLBConj g (Subgroup.zpowers z) ≤ Q →
      GLBConj g (Subgroup.zpowers z) = Subgroup.zpowers z) →
    Q ≤ Subgroup.closure
      {g : G | g ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) ∧ ¬ (3 : ℕ) ∣ orderOf g}

theorem claim113A_clause7 {K Q X A : Subgroup G} {e : G} (hG : Input113dGrun)
    (hsimple : IsSimpleGroup G) (e0 : barOf 3 K ≃* PSL2 (GaloisField 3 3))
    (hX : X = Subgroup.centralizer ({e} : Set G))
    (hQ : IsSylowIn 3 X Q) (hQ1 : Q ≠ ⊥) (hXN : X ≤ Subgroup.normalizer (K : Set G))
    (hKX : K ≤ X) (hK : IsLTwoTwentySeven (barOf 3 K)) (hcyc : IsCyclic ↥(centBar 3 Q K))
    (he3 : e ^ 3 = 1) (he1 : e ≠ 1) (heQ : e ∈ Q)
    (hNK : Subgroup.normalizer (Subgroup.zpowers e : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hAQ : A ≤ Q) (hAel : IsElemAbelian 3 A) (hAcard : Nat.card ↥A = 27)
    (hAmax : ∀ F : Subgroup G, F ≤ ⊤ → IsElemAbelian 3 F → A ≤ F → F = A) :
    ∃ g : G, GLBConj g (Subgroup.zpowers e) ≤ Q ∧
      GLBConj g (Subgroup.zpowers e) ≠ Subgroup.zpowers e := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hcon
  have hcon' : ∀ g : G, GLBConj g (Subgroup.zpowers e) ≤ Q →
      GLBConj g (Subgroup.zpowers e) = Subgroup.zpowers e := by
    intro g hg
    by_contra hne
    exact hcon ⟨g, hg, hne⟩
  have hsylN : IsSylowIn 3 (Subgroup.normalizer (Subgroup.zpowers e : Set G)) Q :=
    isSylowIn_normalizer_zpowers hX hQ he3 he1
  have hord : orderOf e = 3 := orderOf_eq_prime he3 he1
  have hcomm : ∀ q ∈ Q, q * e = e * q := by
    intro q hq
    have hqX : q ∈ X := hQ.1 hq
    rw [hX] at hqX
    exact (Subgroup.mem_centralizer_iff.1 hqX e (Set.mem_singleton e)).symm
  have hGr := hG G e Q hsimple hord hsylN hcomm hcon'
  obtain ⟨x, hxA, hxN⟩ :=
    exists_mem_not_mem_sup hQ hQ1 hXN hKX hK hcyc
      (fun k hk => by
        have hkX : k ∈ X := hKX hk
        rw [hX] at hkX
        exact Subgroup.mem_centralizer_iff.1 hkX e (Set.mem_singleton e))
      he3 he1 heQ hAmax hAel hAcard
  have hxQ : x ∈ Q := hAQ hxA
  have hx3 : x ^ 3 = 1 := hAel.2 x hxA
  have hQK : Q ≤ Subgroup.normalizer (K : Set G) := hQ.1.trans hXN
  have hU27 : Nat.card ↥(Ubar hQK) = 27 := Ubar_card hQ hQ1 hXN hKX hK
  have hxN' : x ∈ Subgroup.normalizer (Subgroup.zpowers e : Set G) := hsylN.1 hxQ
  let N : Subgroup G := Subgroup.normalizer (Subgroup.zpowers e : Set G)
  let Φ : ↥N →* (GaloisField 3 3 ≃+* GaloisField 3 3) :=
    (galHom e0).comp ((barAut 3 K).comp (Subgroup.inclusion hNK))
  have hΦ3 : Nat.card (GaloisField 3 3 ≃+* GaloisField 3 3) = 3 := finite_ringAut_card
  haveI : Finite (GaloisField 3 3 ≃+* GaloisField 3 3) :=
    Nat.finite_of_card_ne_zero (by rw [hΦ3]; norm_num)
  have hΦx : Φ ⟨x, hxN'⟩ ≠ 1 := galHom_rho_ne_one e0 hQ.2.1 hQK hU27 hxQ hx3 hxN
  have hS : Subgroup.closure {g : G | g ∈ N ∧ ¬ (3 : ℕ) ∣ orderOf g} ≤
      (MonoidHom.ker Φ).map N.subtype := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hgN, hg3⟩
    refine ⟨⟨g, hgN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    apply hom_kills_three_prime hΦ3 Φ
    rw [Subgroup.orderOf_mk]
    exact hg3
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 ((hGr.trans hS) hxQ)
  have hn' : n = ⟨x, hxN'⟩ := Subtype.ext hnx
  rw [MonoidHom.mem_ker, hn'] at hn
  exact hΦx hn

end Clause7c

end Lemma113d

open Lemma113d in
theorem lemma113_ii_pieceA_of_inputs (hC : Input113dCentralizer27) (hG : Input113dGrun) :
    Lemma113_ii_pieceAStatement := by
  intro G _ _ m B M E A a e K Q h h0
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDD : IsDDpStar 3 M E A := h.pair
  have hEmax : IsSCp 3 ⊤ E := (lemma104_ii_holds h.toSec10Fails hDD).1
  have hAmax : IsSCp 3 ⊤ A := (lemma104_ii_holds h.toSec10Fails hDD).2
  obtain ⟨hcl1, hQM, hCeN⟩ := Lemma113c.claim113A_clauses_123 h h0
  have hKI : IsLTwoTwentySeven (barOf 3 K) := h.hK.2
  have e0 := Classical.choice hKI
  have hKc : GLAPComponent 3 (Cg e) K := h.hK.1
  have hKX : K ≤ Cg e := h.hK.1.1
  have hQsyl : IsSylowIn 3 (Cg e) Q := h.hQ.1
  have hAQ : A ≤ Q := le_trans le_sup_right h.hQ.2
  have hEQ : E ≤ Q := le_trans le_sup_left h.hQ.2
  have haQ : a ∈ Q := hAQ h.ha.1
  have hQ1 : Q ≠ ⊥ := by
    intro hbot
    rw [hbot] at haQ
    exact h.ha.2 (Subgroup.mem_bot.1 haQ)
  have heA : e ∈ A := (Subgroup.mem_inf.1 h.he.1).2
  have he3 : e ^ 3 = 1 := hAmax.2.1.2 e heA
  have he1 : e ≠ 1 := h.he.2
  have heQ : e ∈ Q := hAQ heA
  have hXe : ∀ x ∈ Cg e, e * x = x * e := fun x hx =>
    Subgroup.mem_centralizer_iff.1 hx e (Set.mem_singleton e)
  have hKe : ∀ k ∈ K, e * k = k * e := fun k hk => hXe k (hKX hk)
  have hEel : IsElemAbelian 3 E := hEmax.2.1
  have hEcard : Nat.card ↥E = 3 ^ 4 := by
    rw [l113_card_eq_pow_pRank hEmax.2.1, h.h4]
  have hAel : IsElemAbelian 3 A := hAmax.2.1
  have hAcard : Nat.card ↥A = 3 ^ 3 := by
    rw [l113_card_eq_pow_pRank hAmax.2.1, h.h3]
  have hAcard27 : Nat.card ↥A = 27 := by rw [hAcard]; norm_num
  have hNK : Subgroup.normalizer (Subgroup.zpowers e : Set G) ≤
      Subgroup.normalizer (K : Set G) :=
    normalizer_zpowers_le_normalizer_K rfl hQsyl hQ1 hCeN hKX hKc hKI he3 he1 hQM haQ h0
  have hcyc : IsCyclic ↥(centBar 3 Q K) :=
    claim113A_clause4 hQsyl hQ1 hCeN hKX hKI hQM haQ h0
  have hcl5 : omegaOne 3 Q = E ⊔ A :=
    omegaOne_eq_of e0 hC hQsyl hQ1 hCeN hKX hKI hcyc hXe he3 he1 heQ hEQ hEel hEcard hAQ hAel
      hAcard hAmax.2.2
  have hcl6 : E = thompsonJ 3 Q :=
    thompsonJ_eq_E e0 hC hQsyl hQ1 hCeN hKX hKI hcyc hKe he3 he1 heQ hEQ hEel hEcard
  have hcl7 := claim113A_clause7 hG h.standing.simple e0 rfl hQsyl hQ1 hCeN hKX hKI hcyc he3 he1
    heQ hNK hAQ hAel hAcard27 hAmax.2.2
  exact ⟨hcl1, hQM, hCeN, hcyc, hcl5, hcl6, hcl7⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround
