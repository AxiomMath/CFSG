module

public import CFSG.CGT.Stroth77.Section33
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.FrameDefs
public import CFSG.Walter.W67.Section5.P56AbAut
import CFSG.GroupTheory.CoprimeCosetFixed

public section

namespace CFSG.CGT.Stroth77.Local

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)

variable {G : Type} [Group G] [Finite G]

theorem exists_odd_complement {D : Subgroup G}
    (hD : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) :
    ∃ O : Subgroup G, O ≤ Subgroup.centralizer (D : Set G) ∧ Odd (Nat.card O) ∧
      ∀ k ∈ Subgroup.centralizer (D : Set G), ∃ d ∈ D, ∃ o ∈ O, k = d * o := by
  obtain ⟨hDK, hDp, hidx⟩ := hD
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.centralizer (D : Set G) with hK
  have hPp : IsPGroup 2 (D.subgroupOf K) :=
    hDp.comap_of_injective K.subtype K.subtype_injective
  let P : Sylow 2 K := hPp.toSylow hidx
  have hP : Subgroup.normalizer ((P : Subgroup K) : Set K) ≤
      Subgroup.centralizer ((P : Subgroup K) : Set K) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyD : (y : G) ∈ D := hy
    exact (Subgroup.mem_centralizer_iff.mp x.2 _ hyD)
  have hc := (MonoidHom.ker_transferSylow_isComplement' P hP).symm
  refine ⟨(MonoidHom.transferSylow P hP).ker.map K.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · have h := MonoidHom.not_dvd_card_ker_transferSylow P hP
    rw [Subgroup.card_map_of_injective K.subtype_injective]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
  · intro k hk
    obtain ⟨⟨⟨p, hp⟩, ⟨t, ht⟩⟩, hpt⟩ := hc.2 ⟨k, hk⟩
    refine ⟨p, hp, t, ⟨t, ht, rfl⟩, ?_⟩
    exact (congrArg Subtype.val hpt).symm

theorem mem_odd_complement_iff {D O : Subgroup G} (hDp : IsPGroup 2 D)
    (hOK : O ≤ Subgroup.centralizer (D : Set G)) (hO : Odd (Nat.card O))
    (hdec : ∀ k ∈ Subgroup.centralizer (D : Set G), ∃ d ∈ D, ∃ o ∈ O, k = d * o) (k : G) :
    k ∈ O ↔ k ∈ Subgroup.centralizer (D : Set G) ∧ Odd (orderOf k) := by
  refine ⟨fun hk => ⟨hOK hk, ?_⟩, fun ⟨hkK, hkodd⟩ => ?_⟩
  · have h := Subgroup.orderOf_dvd_natCard O hk
    exact Odd.of_dvd_nat hO h
  · obtain ⟨d, hd, o, ho, rfl⟩ := hdec k hkK
    have hdo : d * o = o * d := Subgroup.mem_centralizer_iff.mp (hOK ho) d hd
    set n := orderOf (d * o) * Nat.card O with hn
    have hnodd : Odd n := hkodd.mul hO
    have hon : o ^ n = 1 := by
      rw [hn, mul_comm, pow_mul]
      have : o ^ Nat.card O = 1 := by
        have := pow_card_eq_one' (G := O) (x := ⟨o, ho⟩)
        exact congrArg Subtype.val this
      rw [this, one_pow]
    have hkn : (d * o) ^ n = 1 := by
      rw [hn, pow_mul, pow_orderOf_eq_one, one_pow]
    have hdn : d ^ n = 1 := by
      have hcomm : Commute d o := hdo
      rw [hcomm.mul_pow, hon, mul_one] at hkn
      exact hkn
    have hd1 : d = 1 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := (hDp ⟨d, hd⟩)
      have hdj : d ^ 2 ^ j = 1 := congrArg Subtype.val hj
      have h1 : orderOf d ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hdj
      have h2 : orderOf d ∣ n := orderOf_dvd_of_pow_eq_one hdn
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      rcases i with _ | i
      · simpa using hi
      · exfalso
        rw [hi, pow_succ] at h2
        exact (Nat.not_even_iff_odd.mpr hnodd) (even_iff_two_dvd.mpr
          (dvd_trans (dvd_mul_left 2 _) h2))
    rw [hd1, one_mul]
    exact ho

@[expose] def oddCentralizer (D : Subgroup G)
    (hD : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D) : Subgroup G where
  carrier := {k | k ∈ Subgroup.centralizer (D : Set G) ∧ Odd (orderOf k)}
  one_mem' := ⟨one_mem _, by rw [orderOf_one]; exact odd_one⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨O, hOK, hO, hdec⟩ := exists_odd_complement hD
    have key := mem_odd_complement_iff hD.2.1 hOK hO hdec
    have hx' := (key x).mpr hx
    have hy' := (key y).mpr hy
    exact (key _).mp (O.mul_mem hx' hy')
  inv_mem' := by
    intro x hx
    obtain ⟨O, hOK, hO, hdec⟩ := exists_odd_complement hD
    have key := mem_odd_complement_iff hD.2.1 hOK hO hdec
    exact (key _).mp (O.inv_mem ((key x).mpr hx))

section OddCentralizer

variable {D : Subgroup G} (hD : IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D)

theorem mem_oddCentralizer_iff {k : G} :
    k ∈ oddCentralizer D hD ↔ k ∈ Subgroup.centralizer (D : Set G) ∧ Odd (orderOf k) :=
  Iff.rfl

theorem oddCentralizer_le : oddCentralizer D hD ≤ Subgroup.centralizer (D : Set G) :=
  fun _ hk => hk.1

theorem exists_mul_oddCentralizer {k : G} (hk : k ∈ Subgroup.centralizer (D : Set G)) :
    ∃ d ∈ D, ∃ o ∈ oddCentralizer D hD, k = d * o := by
  obtain ⟨O, hOK, hO, hdec⟩ := exists_odd_complement hD
  obtain ⟨d, hd, o, ho, rfl⟩ := hdec k hk
  exact ⟨d, hd, o, (mem_odd_complement_iff hD.2.1 hOK hO hdec o).mp ho, rfl⟩

theorem odd_card_oddCentralizer : Odd (Nat.card (oddCentralizer D hD)) := by
  obtain ⟨O, hOK, hO, hdec⟩ := exists_odd_complement hD
  have e : O = oddCentralizer D hD := by
    ext k
    exact mem_odd_complement_iff hD.2.1 hOK hO hdec k
  rw [← e]
  exact hO

theorem eq_one_of_mem_oddCentralizer {d : G} (hd : d ∈ D) (hdo : d ∈ oddCentralizer D hD) :
    d = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := (hD.2.1 ⟨d, hd⟩)
  have hdj : d ^ 2 ^ j = 1 := congrArg Subtype.val hj
  have h1 : orderOf d ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one hdj
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rcases i with _ | i
  · simpa using hi
  · exfalso
    have hodd := hdo.2
    rw [hi, pow_succ] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_mul_left 2 _))

theorem conj_mem_oddCentralizer {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) {k : G}
    (hk : k ∈ oddCentralizer D hD) : g⁻¹ * k * g ∈ oddCentralizer D hD := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g * y * g⁻¹ ∈ D := by
      have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hg) y).mp hy
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hk.1 _ hy'
    calc y * (g⁻¹ * k * g) = g⁻¹ * ((g * y * g⁻¹) * k) * g := by group
      _ = g⁻¹ * (k * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * k * g * y := by group
  · have : orderOf (g⁻¹ * k * g) = orderOf k := by
      have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective k
      simpa [MulAut.conj_apply] using this
    rw [this]
    exact hk.2

@[expose] noncomputable def conjAut {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    MulAut D where
  toFun x := ⟨g⁻¹ * x * g, (Subgroup.mem_normalizer_iff''.mp hg x).mp x.2⟩
  invFun x := ⟨g * x * g⁻¹, by
    have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hg) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjAut_apply {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (x : D) :
    ((conjAut hg x : D) : G) = g⁻¹ * x * g := rfl

theorem conjAut_pow_apply {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (n : ℕ) (x : D) :
    (((conjAut hg ^ n) x : D) : G) = (g ^ n)⁻¹ * x * g ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, MulAut.mul_apply, ih, conjAut_apply, pow_succ]
    group

theorem exists_two_pow_mem_centralizer (hDp : IsPGroup 2 D) (hcomm : IsMulCommutative D) {g : G}
    (hgN : g ∈ Subgroup.normalizer (D : Set G))
    (hgC : g ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    ∃ a : ℕ, g ^ 2 ^ a ∈ Subgroup.centralizer (D : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, m, hm, hgm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨a, ?_⟩
  set h := g ^ 2 ^ a with hh
  have hhN : h ∈ Subgroup.normalizer (D : Set G) := pow_mem hgN _
  have hhC : h ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := pow_mem hgC _
  have hhm : h ^ m = 1 := by
    rw [hh, ← pow_mul, ← hgm, pow_orderOf_eq_one]
  have hαm : conjAut hhN ^ m = 1 := by
    ext x
    rw [conjAut_pow_apply, hhm]
    simp
  have hcop : Nat.Coprime (orderOf (conjAut hhN)) 2 :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hαm)
      (Nat.coprime_two_right.mpr hm)
  have hfix : ∀ x : D, x ^ 2 = 1 → conjAut hhN x = x := by
    intro x hx
    apply Subtype.ext
    rw [conjAut_apply]
    have hxx : (x : G) * x = 1 := by
      have := congrArg Subtype.val hx
      simpa [pow_two] using this
    have hxO : (x : G) ∈ omegaIn 1 D := ⟨x, Subgroup.subset_closure (by
      change x ^ 2 ^ 1 = 1
      simpa using hx), rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp hhC _ hxO
    rw [mul_assoc, hc]
    group
  have h1 := CFSG.Walter.W67.P56Ab.eq_one_of_forall_pow_eq_one hDp
    (fun x y => hcomm.is_comm.comm x y) (conjAut hhN) hcop hfix
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have := congrArg (fun α : MulAut D => ((α ⟨y, hy⟩ : D) : G)) h1
  simp only [conjAut_apply, MulAut.one_apply] at this
  calc y * h = h * (h⁻¹ * y * h) := by group
    _ = h * y := by rw [this]

end OddCentralizer

section Decomposition

variable {D S : Subgroup G}

theorem le_normalizer_centralizer :
    Subgroup.normalizer (D : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  intro k
  have key : ∀ g ∈ Subgroup.normalizer (D : Set G), ∀ k ∈ Subgroup.centralizer (D : Set G),
      g⁻¹ * k * g ∈ Subgroup.centralizer (D : Set G) := by
    intro g hg k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : g * y * g⁻¹ ∈ D := by
      have := (Subgroup.mem_normalizer_iff''.mp (inv_mem hg) y).mp hy
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.mp hk _ hy'
    calc y * (g⁻¹ * k * g) = g⁻¹ * ((g * y * g⁻¹) * k) * g := by group
      _ = g⁻¹ * (k * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * k * g * y := by group
  refine ⟨key g hg k, fun hk => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hk
  simpa [mul_assoc] using this

theorem le_normalizer_Q :
    Subgroup.normalizer (D : Set G) ≤ Subgroup.normalizer ((Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff'']
  have key : ∀ g ∈ Subgroup.normalizer (D : Set G), ∀ q ∈ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      g⁻¹ * q * g ∈ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
    intro g hg q hq
    obtain ⟨hqN, hqC⟩ := Subgroup.mem_inf.mp hq
    refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hg) hqN) hg,
      Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    have hy' : g * y * g⁻¹ ∈ omegaIn 1 D := by
      have := conj_mem_omegaIn_one (inv_mem hg) hy
      rwa [inv_inv] at this
    have hc := Subgroup.mem_centralizer_iff.mp hqC _ hy'
    calc y * (g⁻¹ * q * g) = g⁻¹ * ((g * y * g⁻¹) * q) * g := by group
      _ = g⁻¹ * (q * (g * y * g⁻¹)) * g := by rw [hc]
      _ = g⁻¹ * q * g * y := by group
  intro q
  refine ⟨key g hg q, fun hq => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hq
  simpa [mul_assoc] using this

theorem isSylowIn_centralizer
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G)) (S ⊓ Subgroup.normalizer (D : Set G))) :
    IsSylowIn 2 (Subgroup.centralizer (D : Set G)) D := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hns' : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ Subgroup.normalizer (D : Set G))
      (Subgroup.normalizer (D : Set G)) := by
    exact CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hns.1, hns.2.1, hns.2.2⟩
  have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (p := 2)
    (P := S ⊓ Subgroup.normalizer (D : Set G)) (K := Subgroup.normalizer (D : Set G))
    (N := Subgroup.centralizer (D : Set G)) hns' (Subgroup.centralizer_le_normalizer _)
    le_normalizer_centralizer
  have e : S ⊓ Subgroup.normalizer (D : Set G) ⊓ Subgroup.centralizer (D : Set G) = D := by
    rw [inf_assoc, inf_eq_right.mpr (Subgroup.centralizer_le_normalizer _), hcent]
  rw [e] at h
  obtain ⟨h1, h2, h3⟩ := CFSG.ABGLocalTools.isSylowOf_iff.mp h
  exact ⟨h1, h2, h3⟩


theorem exists_mul_of_mem_Q (hS : IsPGroup 2 S) (hDS : D ≤ S) (hcomm : IsMulCommutative D)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G)) (S ⊓ Subgroup.normalizer (D : Set G)))
    {q : G} (hqN : q ∈ Subgroup.normalizer (D : Set G))
    (hqC : q ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    ∃ r ∈ S ⊓ Subgroup.normalizer (D : Set G) ⊓
        Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G),
      ∃ o ∈ oddCentralizer D (isSylowIn_centralizer hcent hns), q = r * o := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set hD := isSylowIn_centralizer hcent hns
  set N := Subgroup.normalizer (D : Set G) with hN
  set C1 := Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) with hC1
  set K := Subgroup.centralizer (D : Set G) with hK
  set Q : Subgroup G := N ⊓ C1 with hQ
  set R : Subgroup G := S ⊓ N ⊓ C1 with hR
  set O := oddCentralizer D hD with hO
  have hKN : K ≤ N := Subgroup.centralizer_le_normalizer _
  have hKC1 : K ≤ C1 := Subgroup.centralizer_le (fun x hx => omegaIn_le 1 D hx)
  have hKQ : K ≤ Q := le_inf hKN hKC1
  have hOQ : O ≤ Q := (oddCentralizer_le hD).trans hKQ
  have hRQ : R ≤ Q := fun x hx => Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2, (Subgroup.mem_inf.mp hx).2⟩
  have hDR : D ≤ R := fun x hx => Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hDS hx,
    Subgroup.le_normalizer hx⟩, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      congrArg Subtype.val (hcomm.is_comm.comm ⟨y, omegaIn_le 1 D hy⟩ ⟨x, hx⟩)⟩
  have hRsyl : ¬ 2 ∣ R.relIndex Q := by
    have hns' : CFSG.ABGLocalTools.IsSylowOf 2 (S ⊓ N) N :=
      CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hns.1, hns.2.1, hns.2.2⟩
    have h := CFSG.ABGLocalTools.IsSylowOf.inf_of_le_normalizer (p := 2) hns'
      (inf_le_left : Q ≤ N) le_normalizer_Q
    have e : S ⊓ N ⊓ Q = R := by
      rw [hQ, hR, inf_assoc, ← inf_assoc N N C1, inf_idem, ← inf_assoc]
    rw [e] at h
    exact (CFSG.ABGLocalTools.isSylowOf_iff.mp h).2.2
  have hRO : R ≤ Subgroup.normalizer (O : Set G) := by
    intro r hr
    have hrN : r ∈ N := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hr).1).2
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    refine ⟨fun hh => conj_mem_oddCentralizer hD hrN hh, fun hh => ?_⟩
    have := conj_mem_oddCentralizer hD (inv_mem hrN) hh
    simpa [mul_assoc] using this
  have hKpow : ∃ n : ℕ, K.relIndex Q = 2 ^ n := by
    have hnorm : (K.subgroupOf Q).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKQ).mpr
        ((inf_le_left : Q ≤ N).trans le_normalizer_centralizer)
    have hp : IsPGroup 2 (Q ⧸ K.subgroupOf Q) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H q =>
        obtain ⟨a, ha⟩ := exists_two_pow_mem_centralizer hD.2.1 hcomm
          (Subgroup.mem_inf.mp q.2).1 (Subgroup.mem_inf.mp q.2).2
        refine ⟨a, ?_⟩
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        simpa using ha
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    exact ⟨n, hn⟩
  have hKRO : K ≤ R ⊔ O := by
    intro k hk
    obtain ⟨d, hd, o, ho, rfl⟩ := exists_mul_oddCentralizer hD hk
    exact mul_mem (Subgroup.mem_sup_left (hDR hd)) (Subgroup.mem_sup_right ho)
  have hidx : (R ⊔ O).relIndex Q = 1 := by
    obtain ⟨n, hn⟩ := hKpow
    have h1 : (R ⊔ O).relIndex Q ∣ 2 ^ n :=
      hn ▸ Subgroup.relIndex_dvd_of_le_left Q hKRO
    have h2 : ¬ 2 ∣ (R ⊔ O).relIndex Q := fun h =>
      hRsyl (h.trans (Subgroup.relIndex_dvd_of_le_left Q le_sup_left))
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases i with _ | i
    · simpa using hi
    · exact absurd (hi ▸ dvd_pow_self 2 (Nat.succ_ne_zero i)) h2
  have hq : q ∈ R ⊔ O := Subgroup.relIndex_eq_one.mp hidx (Subgroup.mem_inf.mpr ⟨hqN, hqC⟩)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right R O hRO
  have hq' : q ∈ ((R ⊔ O : Subgroup G) : Set G) := hq
  rw [hset] at hq'
  obtain ⟨r, hr, o, ho, rfl⟩ := hq'
  exact ⟨r, hr, o, ho, rfl⟩

theorem eq_one_of_mem_R_oddCentralizer (hS : IsPGroup 2 S)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G)) (S ⊓ Subgroup.normalizer (D : Set G)))
    {x : G} (hxS : x ∈ S) (hxO : x ∈ oddCentralizer D (isSylowIn_centralizer hcent hns)) :
    x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := hS ⟨x, hxS⟩
  have hxj : x ^ 2 ^ j = 1 := congrArg Subtype.val hj
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hxj)
  rcases i with _ | i
  · simpa using hi
  · exfalso
    have hodd := hxO.2
    rw [hi, pow_succ] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_mul_left 2 _))

theorem eq_of_mul_eq_mul (hS : IsPGroup 2 S)
    (hcent : S ⊓ Subgroup.centralizer (D : Set G) = D)
    (hns : IsSylowIn 2 (Subgroup.normalizer (D : Set G)) (S ⊓ Subgroup.normalizer (D : Set G)))
    {r r' o o' : G} (hr : r ∈ S) (hr' : r' ∈ S)
    (ho : o ∈ oddCentralizer D (isSylowIn_centralizer hcent hns))
    (ho' : o' ∈ oddCentralizer D (isSylowIn_centralizer hcent hns))
    (h : r * o = r' * o') : r = r' := by
  have h1 : r'⁻¹ * r = o' * o⁻¹ := by
    calc r'⁻¹ * r = r'⁻¹ * (r * o) * o⁻¹ := by group
      _ = r'⁻¹ * (r' * o') * o⁻¹ := by rw [h]
      _ = o' * o⁻¹ := by group
  have hmemS : r'⁻¹ * r ∈ S := mul_mem (inv_mem hr') hr
  have hmemO : r'⁻¹ * r ∈ oddCentralizer D (isSylowIn_centralizer hcent hns) :=
    h1 ▸ mul_mem ho' (inv_mem ho)
  have := eq_one_of_mem_R_oddCentralizer hS hcent hns hmemS hmemO
  rw [inv_mul_eq_one] at this
  exact this.symm

end Decomposition

structure Setting (S D : Subgroup G) : Prop where
  isPGroup : IsPGroup 2 S
  le : D ≤ S
  comm : IsMulCommutative D
  cent : S ⊓ Subgroup.centralizer (D : Set G) = D
  nsylow : IsSylowIn 2 (Subgroup.normalizer (D : Set G)) (S ⊓ Subgroup.normalizer (D : Set G))

namespace Setting

variable {S D : Subgroup G} (h : Setting S D)

abbrev O : Subgroup G := oddCentralizer D (isSylowIn_centralizer h.cent h.nsylow)

abbrev R (_ : Setting S D) : Subgroup G := S ⊓ Subgroup.normalizer (D : Set G) ⊓
  Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)

theorem R_le_normalizer : h.R ≤ Subgroup.normalizer (D : Set G) := fun _ hx =>
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2

theorem R_le_S : h.R ≤ S := fun _ hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1

theorem D_le_R : D ≤ h.R := fun x hx => Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨h.le hx,
  Subgroup.le_normalizer hx⟩, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (h.comm.is_comm.comm ⟨y, omegaIn_le 1 D hy⟩ ⟨x, hx⟩)⟩

noncomputable def rPart (q : G) : G := by
  classical
  exact if hq : ∃ r ∈ h.R, ∃ o ∈ h.O, q = r * o then hq.choose else 1

theorem rPart_spec {q : G} (hqN : q ∈ Subgroup.normalizer (D : Set G))
    (hqC : q ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G)) :
    h.rPart q ∈ h.R ∧ ∃ o ∈ h.O, q = h.rPart q * o := by
  have hex : ∃ r ∈ h.R, ∃ o ∈ h.O, q = r * o :=
    exists_mul_of_mem_Q h.isPGroup h.le h.comm h.cent h.nsylow hqN hqC
  have e : h.rPart q = hex.choose := by
    unfold rPart
    rw [dif_pos hex]
  rw [e]
  exact hex.choose_spec

theorem rPart_eq {r o : G} (hr : r ∈ h.R) (ho : o ∈ h.O) : h.rPart (r * o) = r := by
  have hqN : r * o ∈ Subgroup.normalizer (D : Set G) :=
    mul_mem (h.R_le_normalizer hr) ((oddCentralizer_le _).trans
      (Subgroup.centralizer_le_normalizer _) ho)
  have hqC : r * o ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    mul_mem (Subgroup.mem_inf.mp hr).2
      (Subgroup.centralizer_le (fun x hx => omegaIn_le 1 D hx) ((oddCentralizer_le _) ho))
  obtain ⟨hR, o', ho', e⟩ := h.rPart_spec hqN hqC
  exact (eq_of_mul_eq_mul h.isPGroup h.cent h.nsylow (h.R_le_S hR) (h.R_le_S hr) ho' ho
    e.symm)

theorem O_le_centralizer : h.O ≤ Subgroup.centralizer (D : Set G) := oddCentralizer_le _

theorem O_le_normalizer : h.O ≤ Subgroup.normalizer (D : Set G) :=
  h.O_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)

theorem R_le_centralizer_omega :
    h.R ≤ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := fun _ hx =>
  (Subgroup.mem_inf.mp hx).2

theorem conj_mem_Q {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) :
    g⁻¹ * r * g ∈ Subgroup.normalizer (D : Set G) ∧
      g⁻¹ * r * g ∈ Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) := by
  have hq : r ∈ Subgroup.normalizer (D : Set G) ⊓
      Subgroup.centralizer ((omegaIn 1 D : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨h.R_le_normalizer hr, h.R_le_centralizer_omega hr⟩
  have := (Subgroup.mem_normalizer_iff''.mp (le_normalizer_Q hg) r).mp hq
  exact Subgroup.mem_inf.mp this

noncomputable def proj (g r : G) : G := h.rPart (g⁻¹ * r * g)

theorem proj_spec {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) :
    h.proj g r ∈ h.R ∧ ∃ o ∈ h.O, g⁻¹ * r * g = h.proj g r * o :=
  h.rPart_spec (h.conj_mem_Q hg hr).1 (h.conj_mem_Q hg hr).2

theorem proj_mem {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) :
    h.proj g r ∈ h.R :=
  (h.proj_spec hg hr).1

theorem proj_eq_of_mem {g r : G} (h' : g⁻¹ * r * g ∈ h.R) : h.proj g r = g⁻¹ * r * g := by
  unfold proj
  simpa using h.rPart_eq h' (one_mem h.O)

theorem proj_conj_D {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) {d : G}
    (hd : d ∈ D) :
    (h.proj g r)⁻¹ * d * h.proj g r = (g⁻¹ * r * g)⁻¹ * d * (g⁻¹ * r * g) := by
  obtain ⟨hp, o, ho, e⟩ := h.proj_spec hg hr
  set p := h.proj g r
  have hpd : p⁻¹ * d * p ∈ D :=
    (Subgroup.mem_normalizer_iff''.mp (h.R_le_normalizer hp) d).mp hd
  have hc := Subgroup.mem_centralizer_iff.mp (h.O_le_centralizer ho) _ hpd
  rw [e]
  calc p⁻¹ * d * p = o⁻¹ * (o * (p⁻¹ * d * p)) := by group
    _ = o⁻¹ * ((p⁻¹ * d * p) * o) := by rw [hc]
    _ = (p * o)⁻¹ * d * (p * o) := by group

theorem proj_mul_D {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) {d : G}
    (hd : d ∈ D) : h.proj g (r * d) = h.proj g r * (g⁻¹ * d * g) := by
  obtain ⟨hp, o, ho, e⟩ := h.proj_spec hg hr
  have hd' : g⁻¹ * d * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hg d).mp hd
  have hc := Subgroup.mem_centralizer_iff.mp (h.O_le_centralizer ho) _ hd'
  have e' : g⁻¹ * (r * d) * g = (h.proj g r * (g⁻¹ * d * g)) * o := by
    calc g⁻¹ * (r * d) * g = (g⁻¹ * r * g) * (g⁻¹ * d * g) := by group
      _ = h.proj g r * o * (g⁻¹ * d * g) := by rw [e]
      _ = h.proj g r * (o * (g⁻¹ * d * g)) := by group
      _ = h.proj g r * ((g⁻¹ * d * g) * o) := by rw [← hc]
      _ = (h.proj g r * (g⁻¹ * d * g)) * o := by group
  unfold proj
  rw [e']
  exact h.rPart_eq (mul_mem hp (h.D_le_R hd')) ho

theorem proj_twist {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R)
    {x δ : G} (hxS : x ∈ S) (hxN : x ∈ Subgroup.normalizer (D : Set G)) (hδ : δ ∈ D)
    (hx : r⁻¹ * (g * x * g⁻¹) * r = δ * (g * x * g⁻¹)) :
    (h.proj g r)⁻¹ * x * h.proj g r = (g⁻¹ * δ * g) * x := by
  obtain ⟨hp, o, ho, e⟩ := h.proj_spec hg hr
  set p := h.proj g r
  set z := p⁻¹ * x * p with hz
  have hzS : z ∈ S := mul_mem (mul_mem (inv_mem (h.R_le_S hp)) hxS) (h.R_le_S hp)
  have hzN : z ∈ Subgroup.normalizer (D : Set G) :=
    mul_mem (mul_mem (inv_mem (h.R_le_normalizer hp)) hxN) (h.R_le_normalizer hp)
  have hδ' : g⁻¹ * δ * g ∈ D := (Subgroup.mem_normalizer_iff''.mp hg δ).mp hδ
  have h1 : o⁻¹ * z * o = (g⁻¹ * δ * g) * x := by
    have : (g⁻¹ * r * g)⁻¹ * x * (g⁻¹ * r * g) = (g⁻¹ * δ * g) * x := by
      calc (g⁻¹ * r * g)⁻¹ * x * (g⁻¹ * r * g) = g⁻¹ * (r⁻¹ * (g * x * g⁻¹) * r) * g := by
            group
        _ = g⁻¹ * (δ * (g * x * g⁻¹)) * g := by rw [hx]
        _ = (g⁻¹ * δ * g) * x := by group
    rw [e] at this
    rw [hz]
    calc o⁻¹ * (p⁻¹ * x * p) * o = (p * o)⁻¹ * x * (p * o) := by group
      _ = (g⁻¹ * δ * g) * x := this
  have hwO : o⁻¹ * z * o * z⁻¹ ∈ h.O := by
    have h2 : z * o * z⁻¹ ∈ h.O := by
      have := conj_mem_oddCentralizer (isSylowIn_centralizer h.cent h.nsylow) (inv_mem hzN) ho
      simpa [mul_assoc] using this
    have := mul_mem (inv_mem ho) h2
    simpa [mul_assoc] using this
  have hwS : o⁻¹ * z * o * z⁻¹ ∈ S := by
    rw [h1]
    exact mul_mem (mul_mem (h.le hδ') hxS) (inv_mem hzS)
  have hw := eq_one_of_mem_R_oddCentralizer h.isPGroup h.cent h.nsylow hwS hwO
  have hz' : o⁻¹ * z * o = z := by
    calc o⁻¹ * z * o = (o⁻¹ * z * o * z⁻¹) * z := by group
      _ = z := by rw [hw, one_mul]
  rw [← h1, hz']

theorem conj_mem_O {r o : G} (hr : r ∈ h.R) (ho : o ∈ h.O) : r⁻¹ * o * r ∈ h.O :=
  conj_mem_oddCentralizer _ (h.R_le_normalizer hr) ho

theorem proj_mul {g r r' : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R)
    (hr' : r' ∈ h.R) : h.proj g (r * r') = h.proj g r * h.proj g r' := by
  obtain ⟨hp, o, ho, e⟩ := h.proj_spec hg hr
  obtain ⟨hp', o', ho', e'⟩ := h.proj_spec hg hr'
  have hmem : (h.proj g r')⁻¹ * o * h.proj g r' * o' ∈ h.O :=
    mul_mem (h.conj_mem_O hp' ho) ho'
  have key : g⁻¹ * (r * r') * g =
      (h.proj g r * h.proj g r') * ((h.proj g r')⁻¹ * o * h.proj g r' * o') := by
    calc g⁻¹ * (r * r') * g = (g⁻¹ * r * g) * (g⁻¹ * r' * g) := by group
      _ = (h.proj g r * o) * (h.proj g r' * o') := by rw [e, e']
      _ = (h.proj g r * h.proj g r') * ((h.proj g r')⁻¹ * o * h.proj g r' * o') := by group
  unfold proj
  rw [key]
  exact h.rPart_eq (mul_mem hp hp') hmem

theorem proj_one {r : G} (hr : r ∈ h.R) : h.proj 1 r = r :=
  h.proj_eq_of_mem (by simpa using hr) |>.trans (by group)

theorem proj_mul_left {g k r : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hk : k ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) :
    h.proj (g * k) r = h.proj k (h.proj g r) := by
  obtain ⟨hp, o, ho, e⟩ := h.proj_spec hg hr
  obtain ⟨hq, o', ho', e'⟩ := h.proj_spec hk hp
  have ho'' : k⁻¹ * o * k ∈ h.O := conj_mem_oddCentralizer _ hk ho
  have key : (g * k)⁻¹ * r * (g * k) = h.proj k (h.proj g r) * (o' * (k⁻¹ * o * k)) := by
    calc (g * k)⁻¹ * r * (g * k) = k⁻¹ * (g⁻¹ * r * g) * k := by group
      _ = k⁻¹ * (h.proj g r * o) * k := by rw [e]
      _ = (k⁻¹ * h.proj g r * k) * (k⁻¹ * o * k) := by group
      _ = h.proj k (h.proj g r) * o' * (k⁻¹ * o * k) := by rw [e']
      _ = h.proj k (h.proj g r) * (o' * (k⁻¹ * o * k)) := by group
  unfold proj
  rw [key]
  exact h.rPart_eq hq (mul_mem ho' ho'')

theorem proj_pow {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (hr : r ∈ h.R) (n : ℕ) :
    h.proj (g ^ n) r = (h.proj g)^[n] r := by
  induction n generalizing r with
  | zero => simpa using h.proj_one hr
  | succ n ih =>
    rw [pow_succ', h.proj_mul_left hg (pow_mem hg n) hr, Function.iterate_succ_apply,
      ih (h.proj_mem hg hr)]

@[expose] noncomputable def projAut {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    MulAut h.R where
  toFun r := ⟨h.proj g r, h.proj_mem hg r.2⟩
  invFun r := ⟨h.proj g⁻¹ r, h.proj_mem (inv_mem hg) r.2⟩
  left_inv r := Subtype.ext (by
    change h.proj g⁻¹ (h.proj g r) = r
    rw [← h.proj_mul_left hg (inv_mem hg) r.2, mul_inv_cancel, h.proj_one r.2])
  right_inv r := Subtype.ext (by
    change h.proj g (h.proj g⁻¹ r) = r
    rw [← h.proj_mul_left (inv_mem hg) hg r.2, inv_mul_cancel, h.proj_one r.2])
  map_mul' r r' := Subtype.ext (h.proj_mul hg r.2 r'.2)

theorem projAut_apply {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (r : h.R) :
    ((h.projAut hg r : h.R) : G) = h.proj g r := rfl

theorem projAut_pow_apply {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) (n : ℕ)
    (r : h.R) : (((h.projAut hg ^ n) r : h.R) : G) = (h.proj g)^[n] r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', MulAut.mul_apply, projAut_apply, ih, Function.iterate_succ_apply']

theorem orderOf_projAut_dvd {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) :
    orderOf (h.projAut hg) ∣ orderOf g := by
  apply orderOf_dvd_of_pow_eq_one
  ext r
  rw [projAut_pow_apply, ← h.proj_pow hg r.2, pow_orderOf_eq_one, h.proj_one r.2]
  rfl

theorem exists_proj_fixed {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hodd : Odd (orderOf g)) (hr : r ∈ h.R) (hfix : r⁻¹ * h.proj g r ∈ D) :
    ∃ d ∈ D, h.proj g (r * d) = r * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup h.R := D.subgroupOf h.R with hN
  have hND : ∀ n : h.R, n ∈ N ↔ (n : G) ∈ D := fun n => Subgroup.mem_subgroupOf
  have hNinv : ∀ n ∈ N, h.projAut hg n ∈ N := by
    intro n hn
    rw [hND] at hn ⊢
    rw [projAut_apply, h.proj_eq_of_mem (h.D_le_R ((Subgroup.mem_normalizer_iff''.mp hg n).mp hn))]
    exact (Subgroup.mem_normalizer_iff''.mp hg n).mp hn
  have hcard : IsPGroup 2 N := by
    have hD2 : IsPGroup 2 D := h.isPGroup.to_le h.le
    exact hD2.of_equiv (Subgroup.subgroupOfEquivOfLe h.D_le_R).symm
  have hcop : Nat.Coprime (orderOf (h.projAut hg)) (Nat.card N) := by
    obtain ⟨n, hn⟩ := hcard.exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr
      (Odd.of_dvd_nat hodd (h.orderOf_projAut_dvd hg)))
  obtain ⟨n, hn, hfixn⟩ := CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime_mulAut N
    (h.projAut hg) (g := ⟨r, hr⟩) hNinv (by
      rw [hND]
      simpa [projAut_apply] using hfix) hcop
  refine ⟨n, (hND n).mp hn, ?_⟩
  have := congrArg Subtype.val hfixn
  rw [h.proj_mul hg hr n.2]
  simpa [projAut_apply] using this

theorem mul_inv_mem_of_conj_eq {r r' : G} (hr : r ∈ h.R) (hr' : r' ∈ h.R)
    (hconj : ∀ d ∈ D, r⁻¹ * d * r = r'⁻¹ * d * r') : r' * r⁻¹ ∈ D := by
  rw [← h.cent]
  refine Subgroup.mem_inf.mpr ⟨mul_mem (h.R_le_S hr') (inv_mem (h.R_le_S hr)),
    Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
  have := hconj d hd
  calc d * (r' * r⁻¹) = r' * (r'⁻¹ * d * r') * r⁻¹ := by group
    _ = r' * (r⁻¹ * d * r) * r⁻¹ := by rw [this]
    _ = r' * r⁻¹ * d := by group

end Setting

end CFSG.CGT.Stroth77.Local
