module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4G1Defs
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4Rank
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoJ
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer
public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4HbarOrder

public section

namespace CFSG.OddStandard.AltStdSmall4

open Subgroup
open scoped Pointwise

namespace Prop1

variable {G : Type} [Group G] [Finite G]

section Group

private def conjEquiv (g : G) {A B : Subgroup G} (h : ∀ w, w ∈ B ↔ g⁻¹ * w * g ∈ A) :
    A ≃* B where
  toFun a := ⟨g * a * g⁻¹, (h _).2 (by
    rw [show g⁻¹ * (g * (a : G) * g⁻¹) * g = a by group]
    exact a.2)⟩
  invFun b := ⟨g⁻¹ * b * g, (h _).1 b.2⟩
  left_inv a := Subtype.ext (by simp [mul_assoc])
  right_inv b := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

private theorem conj_mem_centralizer_iff (g w a : G) :
    g⁻¹ * w * g ∈ centralizer ({g⁻¹ * a * g} : Set G) ↔ w ∈ centralizer ({a} : Set G) := by
  rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff,
    show g⁻¹ * w * g * (g⁻¹ * a * g) = g⁻¹ * (w * a) * g by group,
    show g⁻¹ * a * g * (g⁻¹ * w * g) = g⁻¹ * (a * w) * g by group, mul_left_inj, mul_right_inj]

private theorem orderOf_conj_inv (g a : G) : orderOf (g⁻¹ * a * g) = orderOf a := by
  rw [show g⁻¹ * a * g = MulAut.conj g⁻¹ a by simp [MulAut.conj_apply], MulEquiv.orderOf_eq]

private theorem comm_of_sq {T : Subgroup G} (hT : ∀ x ∈ T, x ^ 2 = 1) {a b : G} (ha : a ∈ T)
    (hb : b ∈ T) : a * b = b * a := by
  have hi : ∀ w ∈ T, w⁻¹ = w := fun w hw =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hT w hw)
  calc a * b = (a * b)⁻¹ := (hi _ (T.mul_mem ha hb)).symm
    _ = b * a := by rw [mul_inv_rev, hi b hb, hi a ha]

private theorem isPGroup_of_sq {T : Subgroup G} (hT : ∀ x ∈ T, x ^ 2 = 1) : IsPGroup 2 T :=
  fun x => ⟨1, Subtype.ext (by simpa using hT x x.2)⟩

private theorem card_mul_le {A K P : Subgroup G} (hA : A ≤ P) (hK : K ≤ P) :
    Nat.card K * Nat.card A ≤ Nat.card (A ⊓ K : Subgroup G) * Nat.card P := by
  have h1 := relIndex_mul_card A K
  have h2 := relIndex_mul_card A P
  rw [inf_eq_left.2 hA] at h2
  have hne : A.relIndex P ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := P)).ne' h2.symm
  have h3 := relIndex_le_of_le_right hK hne
  calc Nat.card K * Nat.card A
      = A.relIndex K * Nat.card A * Nat.card (A ⊓ K : Subgroup G) := by rw [← h1]; ring
    _ ≤ A.relIndex P * Nat.card A * Nat.card (A ⊓ K : Subgroup G) := by gcongr
    _ = Nat.card (A ⊓ K : Subgroup G) * Nat.card P := by rw [← h2]; ring

private theorem card_eq_card_sylow {K M M' : Subgroup G} (hKM : K ≤ M) (hK : IsPGroup 2 K)
    (hidx : ¬ 2 ∣ K.relIndex M) (hMM' : Nat.card M = Nat.card M') (P : Sylow 2 M') :
    Nat.card K = Nat.card P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (K.subgroupOf M) := hK.of_equiv (subgroupOfEquivOfLe hKM).symm
  have h1 : Nat.card (K.subgroupOf M) = 2 ^ Nat.factorization (Nat.card M) 2 :=
    Sylow.card_eq_multiplicity (hp.toSylow hidx)
  rw [← Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv, h1, hMM',
    Sylow.card_eq_multiplicity P]

private theorem exists_mem_normalizer_not_mem {P : Subgroup G} (hP : IsPGroup 2 P)
    (h2 : 2 ∣ P.index) : ∃ y ∈ normalizer (P : Set G), y ∉ P ∧ IsPGroup 2 (zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hPS'⟩ := hP.exists_le_sylow
  have hne : P ≠ (S' : Subgroup G) := fun heq => S'.not_dvd_index (heq ▸ h2)
  have hnil : Group.IsNilpotent (S' : Subgroup G) := S'.isPGroup'.isNilpotent
  have hlt : P.subgroupOf (S' : Subgroup G) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => hne (le_antisymm hPS' fun s hs => ?_)
    have : (⟨s, hs⟩ : (S' : Subgroup G)) ∈ P.subgroupOf (S' : Subgroup G) := by
      rw [htop]
      trivial
    exact this
  obtain ⟨⟨y, hyS'⟩, hyN, hyP⟩ := IsConcreteLE.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (P.subgroupOf (S' : Subgroup G)) hlt)
  refine ⟨y, mem_normalizer_iff.2 fun h => ⟨fun hh => ?_, fun hh => ?_⟩, fun h => hyP h,
    S'.isPGroup'.to_le (zpowers_le.2 hyS')⟩
  · exact (mem_normalizer_iff.1 hyN ⟨h, hPS' hh⟩).1 hh
  · have hhS' : h ∈ (S' : Subgroup G) := by
      rw [show h = y⁻¹ * (y * h * y⁻¹) * y by group]
      exact S'.mul_mem (S'.mul_mem (S'.inv_mem hyS') (hPS' hh)) hyS'
    exact (mem_normalizer_iff.1 hyN ⟨h, hhS'⟩).2 hh

end Group

variable {L Q : Subgroup G} {n : ℕ} {θ : L ≃* alternatingGroup (Fin n)} {z : G}
  {c : Config G L Q n θ z} {T S₀ D : Subgroup G}

private theorem E_le (hn : 8 ≤ n) : E θ hn ≤ L := by
  unfold E
  exact map_subtype_le _

private theorem z_ne_mul (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T) {q l : G}
    (hq : q ∈ T) (hl : l ∈ L) : z ≠ q * l := by
  intro hzql
  have hlz : l⁻¹ * z = z * l⁻¹ :=
    mem_centralizer_iff.1 (c.ot.cyc.le c.ot.cyc.mem) l⁻¹ (L.inv_mem hl)
  have hqC : q ∈ T ⊓ centralizer ({z} : Set G) := by
    refine mem_inf.2 ⟨hq, ?_⟩
    rw [mem_centralizer_singleton_iff, show q = z * l⁻¹ by rw [hzql]; group, mul_assoc, hlz]
  rw [hH.n0.cent] at hqC
  exact AltStdCycTwo.not_conj_mem_L c.ot.std θ c.hn8 c.ot.cyc c.ot.card 1
    (by rw [one_mul, inv_one, mul_one, hzql]; exact L.mul_mem (E_le c.hn8 hqC) hl)

private theorem card_cent_T (c : Config G L Q n θ z) (hH : HData θ c.hn8 z T) :
    Nat.card (T ⊓ centralizer ({z} : Set G) : Subgroup G) = 8 := by
  have hz : z * z = 1 := by rw [← sq, ← c.ot.cyc.order, pow_orderOf_eq_one]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hzT : ∀ x ∈ T, z * x * z⁻¹ ∈ T := fun x hx => (mem_normalizer_iff.1 hH.n0.norm x).1 hx
  let f : T →* T :=
    { toFun := fun x => ⟨x * (z * (x : G)⁻¹ * z⁻¹), T.mul_mem x.2 (hzT _ (T.inv_mem x.2))⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        show (a : G) * b * (z * ((a : G) * b)⁻¹ * z⁻¹) =
          a * (z * (a : G)⁻¹ * z⁻¹) * (b * (z * (b : G)⁻¹ * z⁻¹))
        have h := comm_of_sq hH.elem (hzT _ (T.inv_mem a.2))
          (T.mul_mem b.2 (hzT _ (T.inv_mem b.2)))
        calc (a : G) * b * (z * ((a : G) * b)⁻¹ * z⁻¹)
            = a * ((b * (z * (b : G)⁻¹ * z⁻¹)) * (z * (a : G)⁻¹ * z⁻¹)) := by group
          _ = a * ((z * (a : G)⁻¹ * z⁻¹) * (b * (z * (b : G)⁻¹ * z⁻¹))) := by rw [← h]
          _ = a * (z * (a : G)⁻¹ * z⁻¹) * (b * (z * (b : G)⁻¹ * z⁻¹)) := by group) }
  have hker : f.ker = (T ⊓ centralizer ({z} : Set G)).subgroupOf T := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : (x : G) * (z * (x : G)⁻¹ * z⁻¹) = 1 := congrArg Subtype.val h
      exact ⟨x.2, by
        rw [show (x : G) * z = (x * (z * (x : G)⁻¹ * z⁻¹)) * z * x by group, h', one_mul]⟩
    · rintro ⟨-, h⟩
      refine Subtype.ext (show (x : G) * (z * (x : G)⁻¹ * z⁻¹) = 1 from ?_)
      rw [show (x : G) * (z * (x : G)⁻¹ * z⁻¹) = x * z * (x : G)⁻¹ * z⁻¹ by group, h]
      group
  have hrange : f.range = (T ⊓ centralizer ({z} : Set G)).subgroupOf T := by
    ext y
    rw [MonoidHom.mem_range, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(f x).2, ?_⟩
      have hxi : (x : G)⁻¹ = x :=
        inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hH.elem x x.2)
      have h := comm_of_sq hH.elem x.2 (show z * x * z ∈ T by simpa [hzi] using hzT x x.2)
      show (x : G) * (z * (x : G)⁻¹ * z⁻¹) * z = z * ((x : G) * (z * (x : G)⁻¹ * z⁻¹))
      rw [hxi, hzi]
      calc (x : G) * (z * x * z) * z = x * z * x * (z * z) := by group
        _ = (z * z) * (x * z * x) := by rw [hz, mul_one, one_mul]
        _ = z * ((z * x * z) * x) := by group
        _ = z * (x * (z * x * z)) := by rw [← h]
    · rintro ⟨-, hyz⟩
      have hyy : (y : G) * y = 1 := by rw [← sq]; exact hH.elem y y.2
      have hy2 : ((y : G) * z) ^ 2 = 1 := by
        rw [sq, show (y : G) * z * (y * z) = y * (z * y) * z by group, ← hyz,
          show (y : G) * (y * z) * z = (y * y) * (z * z) by group, hyy, hz, one_mul]
      obtain ⟨x, hxT, hx⟩ := hH.inv y y.2 hy2
      refine ⟨⟨x, hxT⟩, Subtype.ext (show x * (z * x⁻¹ * z⁻¹) = y from ?_)⟩
      rw [show x * (z * x⁻¹ * z⁻¹) = x * z * x⁻¹ * z⁻¹ by group, hx]
      group
  have hcard := card_ker_mul_card_range f
  rw [hker, hrange, Nat.card_congr (subgroupOfEquivOfLe
    (inf_le_left : T ⊓ centralizer ({z} : Set G) ≤ T)).toEquiv, hH.n0.card_eq] at hcard
  exact Nat.mul_self_inj.1 (hcard.trans (by norm_num))

private theorem T_le_TB : T ≤ TB T S₀ := le_sup_left

private theorem S₀_le_TB : S₀ ≤ TB T S₀ := le_sup_right

private theorem exists_of_mem_MB (hd : G1Data c T S₀ D) {x : G} (hx : x ∈ MB T D) :
    ∃ q ∈ T, ∃ d ∈ D, q * d = x := by
  have h : x ∈ (T : Set G) * (D : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left T D (hd.D_le_S₀.trans hd.S₀_norm)]
    exact hx
  exact Set.mem_mul.1 h

private theorem z_not_mem_MB (hd : G1Data c T S₀ D) : z ∉ MB T D := by
  intro hz
  obtain ⟨q, hq, d, hdD, hqd⟩ := exists_of_mem_MB hd hz
  exact z_ne_mul c hd.hH hq (hd.D_le_L hdD) hqd.symm

private theorem MB_le_TB (hd : G1Data c T S₀ D) : MB T D ≤ TB T S₀ :=
  sup_le_sup_left hd.D_le_S₀ T

private theorem TB_le (hd : G1Data c T S₀ D) : TB T S₀ ≤ normalizer (T : Set G) :=
  sup_le le_normalizer hd.S₀_norm

private theorem isPGroup_TB (hd : G1Data c T S₀ D) : IsPGroup 2 (TB T S₀) :=
  (isPGroup_of_sq hd.hH.elem).to_sup_of_normal_left' hd.S₀_p hd.S₀_norm

private theorem card_TB_ge (hd : G1Data c T S₀ D) : 2 ^ 10 ≤ Nat.card (TB T S₀) := by
  have h := card_mul_le (A := T) (K := S₀) (P := TB T S₀) T_le_TB S₀_le_TB
  have h8 : Nat.card (T ⊓ S₀ : Subgroup G) ≤ 8 := by
    rw [← card_cent_T c hd.hH]
    exact card_le_of_le (inf_le_inf_left T (hd.S₀_le.trans inf_le_right))
  rw [hd.S₀_card, hd.hH.n0.card_eq] at h
  have h' := h.trans (Nat.mul_le_mul_right (Nat.card (TB T S₀)) h8)
  norm_num at h' ⊢
  omega

private theorem card_MB_ge (hd : G1Data c T S₀ D) : 2 ^ 9 ≤ Nat.card (MB T D) := by
  have h := card_mul_le (A := T) (K := D) (P := MB T D) le_sup_left le_sup_right
  rw [inf_comm, hd.D_inf, card_bot, one_mul, hd.D_card, hd.hH.n0.card_eq] at h
  norm_num at h ⊢
  omega

private theorem card_le_of_pgroup (h11 : ¬ 2 ^ 11 ∣ Nat.card (normalizer (T : Set G)))
    {R : Subgroup G} (hR : IsPGroup 2 R) (hRH : R ≤ normalizer (T : Set G)) :
    Nat.card R ≤ 2 ^ 10 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
  have hdvd : 2 ^ k ∣ Nat.card (normalizer (T : Set G)) := hk ▸ card_dvd_of_le hRH
  rw [hk]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  by_contra hk10
  exact h11 ((pow_dvd_pow 2 (by omega : 11 ≤ k)).trans hdvd)

private theorem eq_TB (hd : G1Data c T S₀ D) (h11 : ¬ 2 ^ 11 ∣ Nat.card (normalizer (T : Set G)))
    {R : Subgroup G} (hR : IsPGroup 2 R) (hle : TB T S₀ ≤ R) (hRH : R ≤ normalizer (T : Set G)) :
    R = TB T S₀ :=
  (eq_of_le_of_card_ge hle ((card_le_of_pgroup h11 hR hRH).trans (card_TB_ge hd))).symm

private theorem card_TB (hd : G1Data c T S₀ D)
    (h11 : ¬ 2 ^ 11 ∣ Nat.card (normalizer (T : Set G))) : Nat.card (TB T S₀) = 2 ^ 10 :=
  le_antisymm (card_le_of_pgroup h11 (isPGroup_TB hd) (TB_le hd)) (card_TB_ge hd)

private theorem z_mem_TB (hd : G1Data c T S₀ D)
    (h11 : ¬ 2 ^ 11 ∣ Nat.card (normalizer (T : Set G))) : z ∈ TB T S₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.ot.cyc.order, pow_one])
  have hzS : zpowers z ≤ normalizer (S₀ : Set G) :=
    (zpowers_le.2 (mem_centralizer_iff.2 fun s hs =>
      mem_centralizer_singleton_iff.1 (hd.S₀_le hs).2)).trans (centralizer_le_normalizer _)
  have hK : S₀ ⊔ zpowers z ≤ normalizer (T : Set G) :=
    sup_le hd.S₀_norm (zpowers_le.2 hd.hH.n0.norm)
  have hR := eq_TB hd h11 ((isPGroup_of_sq hd.hH.elem).to_sup_of_normal_left'
    (hd.S₀_p.to_sup_of_normal_left' hzp hzS) hK) (sup_le_sup_left le_sup_left T)
    (sup_le le_normalizer hK)
  rw [← hR]
  exact mem_sup_right (mem_sup_right (mem_zpowers z))

private theorem cent_TB (hd : G1Data c T S₀ D) (hTB : Nat.card (TB T S₀) = 2 ^ 10) :
    TB T S₀ ⊓ centralizer ({z} : Set G) = S₀ := by
  have hle : S₀ ≤ TB T S₀ ⊓ centralizer ({z} : Set G) :=
    le_inf S₀_le_TB (hd.S₀_le.trans inf_le_right)
  refine (eq_of_le_of_card_ge hle ?_).symm
  have h := card_mul_le (A := T) (K := TB T S₀ ⊓ centralizer ({z} : Set G)) (P := TB T S₀)
    T_le_TB inf_le_left
  have h8 : Nat.card (T ⊓ (TB T S₀ ⊓ centralizer ({z} : Set G)) : Subgroup G) ≤ 8 := by
    rw [← card_cent_T c hd.hH]
    exact card_le_of_le (inf_le_inf_left T inf_le_right)
  rw [hd.hH.n0.card_eq, hTB] at h
  rw [hd.S₀_card]
  have h' := h.trans (Nat.mul_le_mul_right _ h8)
  norm_num at h' ⊢
  omega

private theorem relIndex_MB (hd : G1Data c T S₀ D) (hTB : Nat.card (TB T S₀) = 2 ^ 10)
    (hz : z ∈ TB T S₀) : (MB T D).relIndex (TB T S₀) = 2 := by
  have h := relIndex_mul_card (MB T D) (TB T S₀)
  rw [inf_eq_left.2 (MB_le_TB hd), hTB] at h
  have h1 : (MB T D).relIndex (TB T S₀) ≠ 1 := fun h1 =>
    z_not_mem_MB hd (relIndex_eq_one.1 h1 hz)
  have h0 : (MB T D).relIndex (TB T S₀) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h
    norm_num at h
  have h2 := Nat.mul_le_mul_left ((MB T D).relIndex (TB T S₀)) (card_MB_ge hd)
  rw [h] at h2
  norm_num at h2
  omega

private theorem conj_mem_MB (hd : G1Data c T S₀ D) (hrel : (MB T D).relIndex (TB T S₀) = 2)
    {t x : G} (ht : t ∈ TB T S₀) (hx : x ∈ MB T D) : t * x * t⁻¹ ∈ MB T D := by
  have hn : ((MB T D).subgroupOf (TB T S₀)).Normal := normal_of_index_eq_two hrel
  exact hn.conj_mem ⟨x, MB_le_TB hd hx⟩ hx ⟨t, ht⟩

private theorem not_conj_mem_cent (h1 : Sec4TwoElemN0) (hd : G1Data c T S₀ D)
    (hS : TB T S₀ ⊓ centralizer ({z} : Set G) = S₀) (hrel : (MB T D).relIndex (TB T S₀) = 2)
    (a : G) (ha : a * z * a⁻¹ ∈ MB T D) {t : G} (ht : t ∈ TB T S₀) :
    t * (a * z * a⁻¹) * t⁻¹ ∉ centralizer ({z} : Set G) := by
  intro hc
  have hyM := conj_mem_MB hd hrel ht ha
  have hyS : t * (a * z * a⁻¹) * t⁻¹ ∈ S₀ := hS ▸ ⟨MB_le_TB hd hyM, hc⟩
  have hyc : t * (a * z * a⁻¹) * t⁻¹ = (t * a) * z * (t * a)⁻¹ := by group
  have hz2 : z ^ 2 = 1 := c.ot.cyc.order ▸ pow_orderOf_eq_one z
  have hy2 : (t * (a * z * a⁻¹) * t⁻¹) ^ 2 ^ 1 = 1 := by
    rw [hyc, pow_one, conj_pow, hz2, mul_one, mul_inv_cancel]
  obtain ⟨m, hm, hym | hym⟩ := h1 G L Q n θ z c _ (hd.S₀_le hyS) 1 hy2
  · exact AltStdCycTwo.not_conj_mem_L c.ot.std θ c.hn8 c.ot.cyc c.ot.card (t * a)
      (by rw [← hyc, hym]; exact hm)
  · obtain ⟨q, hq, d, hdD, hqd⟩ := exists_of_mem_MB hd hyM
    exact z_ne_mul c hd.hH hq (L.mul_mem (hd.D_le_L hdD) (L.inv_mem hm))
      (by rw [← mul_assoc, hqd, hym]; group)

private theorem caseA (h1 : Sec4TwoElemN0) (h2 : Sec4CentSylowCard) (hd : G1Data c T S₀ D)
    (hf : TBFacts T S₀ D z) (hS : TB T S₀ ⊓ centralizer ({z} : Set G) = S₀)
    (hz : z ∈ TB T S₀) (hrel : (MB T D).relIndex (TB T S₀) = 2)
    (hA : ¬ 2 ∣ (TB T S₀).index) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := c.ot.std.simple
  have hz2 : z ^ 2 = 1 := c.ot.cyc.order ▸ pow_orderOf_eq_one z
  obtain ⟨g, hgM, hext, hcent⟩ :=
    CFSG.ComponentClassification.HarrisLit.HarrisEnd.exists_extremal_conj_of_relIndex_two
      c.ot.std.nonab (isPGroup_TB hd) hA (MB_le_TB hd) hrel hz (z_not_mem_MB hd) hz2
  obtain ⟨hle, hp, hidx⟩ := hext
  have hxT : g⁻¹ * z * g ∉ T := by
    have := conj_not_mem_of_elementary c hd.hH.elem hd.hH.n0.card_eq g⁻¹
    rwa [inv_inv] at this
  have hxo : orderOf (g⁻¹ * z * g) = 2 := (orderOf_conj_inv g z).trans c.ot.cyc.order
  obtain ⟨P⟩ : Nonempty (Sylow 2 (centralizer ({z} : Set G))) := inferInstance
  have hKP : Nat.card (TB T S₀ ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) =
      Nat.card P :=
    card_eq_card_sylow hle hp hidx
      (Nat.card_congr (conjEquiv g fun w => (conj_mem_centralizer_iff g w z).symm).toEquiv) P
  have hdisj : Nat.card (TB T S₀ ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) = 2 ^ 8 ∨
      Nonempty ((TB T S₀ ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) ≃*
        (TB T S₀ ⊓ centralizer ({z} : Set G) : Subgroup G)) := by
    by_cases hc : IsASmall L n z
    · have h7 := (h2 G L Q n θ z c P).1 hc
      let φ : (TB T S₀ ⊓ centralizer ({z} : Set G) : Subgroup G) →*
          (TB T S₀ ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) :=
        { toFun := fun w => ⟨g⁻¹ * w * g, hcent w w.2⟩
          map_one' := Subtype.ext (by simp)
          map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
      have hinj : Function.Injective φ := fun a b hab => by
        have h : g⁻¹ * (a : G) * g = g⁻¹ * (b : G) * g := congrArg Subtype.val hab
        exact Subtype.ext (mul_left_cancel (mul_right_cancel h))
      have hcard : Nat.card (TB T S₀ ⊓ centralizer ({z} : Set G) : Subgroup G) =
          Nat.card (TB T S₀ ⊓ centralizer ({g⁻¹ * z * g} : Set G) : Subgroup G) := by
        rw [hS, hd.S₀_card, hKP, h7]
      exact Or.inr ⟨(MulEquiv.ofBijective φ
        ((Nat.bijective_iff_injective_and_card φ).2 ⟨hinj, hcard⟩)).symm⟩
    · exact Or.inl (hKP.trans ((h2 G L Q n θ z c P).2 hc))
  obtain ⟨t, ht, htc⟩ := hf.conj_cent _ hgM hxT hxo hdisj
  exact not_conj_mem_cent h1 hd hS hrel g⁻¹ (by rwa [inv_inv]) ht (by rwa [inv_inv])

private theorem caseB (h1 : Sec4TwoElemN0) (hd : G1Data c T S₀ D) (hf : TBFacts T S₀ D z)
    (h11 : ¬ 2 ^ 11 ∣ Nat.card (normalizer (T : Set G)))
    (hS : TB T S₀ ⊓ centralizer ({z} : Set G) = S₀) (hz : z ∈ TB T S₀)
    (hrel : (MB T D).relIndex (TB T S₀) = 2) (hB : 2 ∣ (TB T S₀).index) : False := by
  obtain ⟨y, hyN, hyTB, hyp⟩ := exists_mem_normalizer_not_mem (isPGroup_TB hd) hB
  have hyH : y ∉ normalizer (T : Set G) := by
    intro hyH
    have hR := eq_TB hd h11 ((isPGroup_TB hd).to_sup_of_normal_left' hyp (zpowers_le.2 hyN))
      le_sup_left (sup_le (TB_le hd) (zpowers_le.2 hyH))
    exact hyTB (hR ▸ mem_sup_right (mem_zpowers y))
  have hyTB' : ∀ w, w ∈ TB T S₀ ↔ y⁻¹ * w * y ∈ TB T S₀ := mem_normalizer_iff''.1 hyN
  have hmemN : ∀ w, w ∈ conjSub y T ↔ y⁻¹ * w * y ∈ T := by
    intro w
    constructor
    · rintro ⟨t, ht, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using ht
    · intro hw
      exact mem_map.2 ⟨y⁻¹ * w * y, hw, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hNle : conjSub y T ≤ TB T S₀ := fun w hw => (hyTB' w).2 (T_le_TB ((hmemN w).1 hw))
  have hNnorm : ∀ g ∈ TB T S₀, ∀ w ∈ conjSub y T, g * w * g⁻¹ ∈ conjSub y T := by
    intro g hg w hw
    rw [hmemN] at hw ⊢
    rw [show y⁻¹ * (g * w * g⁻¹) * y = (y⁻¹ * g * y) * (y⁻¹ * w * y) * (y⁻¹ * g * y)⁻¹ by group]
    exact (mem_normalizer_iff.1 (TB_le hd ((hyTB' g).1 hg)) _).1 hw
  have hNsq : ∀ w ∈ conjSub y T, w ^ 2 = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_pow, hd.hH.elem t ht, map_one]
  have hNcard : Nat.card (conjSub y T) = 64 := by
    rw [conjSub, card_map_of_injective (MulAut.conj y).injective, hd.hH.n0.card_eq]
  have hNT : conjSub y T ≠ T := by
    intro hNT
    apply hyH
    rw [mem_normalizer_iff'']
    intro w
    rw [← hmemN, hNT]
  have h16 := hf.normal_e64 _ hNle hNnorm hNsq hNcard hNT
  have hxTB : y⁻¹ * z * y ∈ TB T S₀ := (hyTB' z).1 hz
  have hxT : y⁻¹ * z * y ∉ T := by
    have := conj_not_mem_of_elementary c hd.hH.elem hd.hH.n0.card_eq y⁻¹
    rwa [inv_inv] at this
  have hxo : orderOf (y⁻¹ * z * y) = 2 := (orderOf_conj_inv y z).trans c.ot.cyc.order
  have hx2 : (y⁻¹ * z * y) ^ 2 = 1 := hxo ▸ pow_orderOf_eq_one _
  have hcT : Nat.card (T ⊓ centralizer ({y⁻¹ * z * y} : Set G) : Subgroup G) = 16 := by
    rw [← h16]
    exact Nat.card_congr (conjEquiv y (A := T ⊓ centralizer ({y⁻¹ * z * y} : Set G))
      (B := conjSub y T ⊓ centralizer ({z} : Set G)) fun w => by
        rw [mem_inf, mem_inf, hmemN, conj_mem_centralizer_iff]).toEquiv
  have hxM := hf.mem_MB _ hxTB hxT hx2 hcT
  have hiso : Nonempty ((TB T S₀ ⊓ centralizer ({y⁻¹ * z * y} : Set G) : Subgroup G) ≃*
      (TB T S₀ ⊓ centralizer ({z} : Set G) : Subgroup G)) :=
    ⟨conjEquiv y fun w => by rw [mem_inf, mem_inf, ← hyTB', conj_mem_centralizer_iff]⟩
  obtain ⟨t, ht, htc⟩ := hf.conj_cent _ hxM hxT hxo (Or.inr hiso)
  exact not_conj_mem_cent h1 hd hS hrel y⁻¹ (by rwa [inv_inv]) ht (by rwa [inv_inv])

end Prop1

theorem sec4HTwoPart_of_parts (h1 : Sec4TwoElemN0) (h2 : Sec4CentSylowCard)
    (h3 : Sec4ExistsG1Data) (h4 : Sec4TBFacts) : Sec4HTwoPart := by
  intro G _ _ L Q n θ z c T hH
  obtain ⟨S₀, D, hd⟩ := h3 G L Q n θ z c T hH
  have hf := h4 G L Q n θ z c T S₀ D hd
  by_contra h11
  have hTB := Prop1.card_TB hd h11
  have hz := Prop1.z_mem_TB hd h11
  have hS := Prop1.cent_TB hd hTB
  have hrel := Prop1.relIndex_MB hd hTB hz
  by_cases hA : 2 ∣ (TB T S₀).index
  · exact Prop1.caseB h1 hd hf h11 hS hz hrel hA
  · exact Prop1.caseA h1 h2 hd hf hS hz hrel hA

end CFSG.OddStandard.AltStdSmall4
