module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Reduce
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.CommutingPair (exists_pow_mul_pow_of_mem)

section Pair

variable {X : Type*} [Group X]

theorem card_closure_pair_sq [Finite X] {p : ℕ} [hp : Fact p.Prime] {a b : X} (h : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1) (ha1 : a ≠ 1) (hba : b ∉ Subgroup.zpowers a) :
    Nat.card (Subgroup.closure ({a, b} : Set X)) = p ^ 2 := by
  set K := Subgroup.closure ({a, b} : Set X) with hK
  have hp0 : 0 < p := hp.out.pos
  have hexp : ∀ g ∈ K, g ^ p = 1 := by
    intro g hg
    obtain ⟨i, -, j, -, rfl⟩ := exists_pow_mul_pow_of_mem hp0 h ha hb hg
    rw [(h.pow_pow i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm j, pow_mul, pow_mul,
      ha, hb, one_pow, one_pow, mul_one]
  have hpK : IsPGroup p K := fun g =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hexp _ g.2)⟩
  obtain ⟨k, hk⟩ := hpK.exists_card_eq
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have haK : a ∈ K := Subgroup.subset_closure (by simp)
  have hbK : b ∈ K := Subgroup.subset_closure (by simp)
  have hz : Subgroup.zpowers a ≤ K := (Subgroup.zpowers_le).2 haK
  have hup : Nat.card K ≤ p ^ 2 := by
    let f : Fin p × Fin p → K := fun ij =>
      ⟨a ^ (ij.1 : ℕ) * b ^ (ij.2 : ℕ), mul_mem (pow_mem haK _) (pow_mem hbK _)⟩
    have hf : Function.Surjective f := by
      rintro ⟨g, hg⟩
      obtain ⟨i, hi, j, hj, rfl⟩ := exists_pow_mul_pow_of_mem hp0 h ha hb hg
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩), rfl⟩
    have h2 := Nat.card_le_card_of_surjective f hf
    have h3 : Nat.card (Fin p × Fin p) = p * p := by simp [Nat.card_prod]
    rw [h3] at h2
    nlinarith
  have hbz : b ∉ Subgroup.zpowers a := hba
  have hk1 : 2 ≤ k := by
    by_contra hk1
    push Not at hk1
    have hle : Nat.card (Subgroup.zpowers a) ≤ Nat.card K := Subgroup.card_le_of_le hz
    have hKle : Nat.card K ≤ p := by
      rw [hk]
      interval_cases k <;> simp <;> omega
    have heq : Subgroup.zpowers a = K := Subgroup.eq_of_le_of_card_ge hz (by
      rw [Nat.card_zpowers, hord]; exact hKle)
    exact hbz (heq ▸ hbK)
  have hk2 : k ≤ 2 := by
    by_contra hk3
    push Not at hk3
    have : p ^ 3 ≤ p ^ k := Nat.pow_le_pow_right hp0 hk3
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.out.one_lt (by norm_num)
    omega
  rw [hk, le_antisymm hk2 hk1]

end Pair

section Line

variable {X : Type*} [Group X] {p : ℕ}

structure SevenLine (p : ℕ) (w : X) (F : Subgroup X) : Prop where
  ne_one : w ≠ 1
  pow_eq : w ^ p = 1
  mem : w ∈ F
  le_cent : F ≤ Subgroup.centralizer ({w} : Set X)
  card_eq : Nat.card F = p ^ 3
  syl : ∀ c ∈ Subgroup.centralizer ({w} : Set X), (∃ n : ℕ, c ^ (p ^ n) = 1) → c ∈ F
  norm : ∀ c ∈ Subgroup.centralizer ({w} : Set X), ∀ f ∈ F, c * f * c⁻¹ ∈ F
  cent : ∀ c ∈ Subgroup.centralizer ({w} : Set X), (∀ f ∈ F, c * f = f * c) →
    c ∈ Subgroup.zpowers w

variable {w : X} {F : Subgroup X}

theorem SevenLine.comm_w (h : SevenLine p w F) {f : X} (hf : f ∈ F) : w * f = f * w :=
  (Subgroup.mem_centralizer_singleton_iff.1 (h.le_cent hf)).symm

theorem SevenLine.center_le (h : SevenLine p w F) {x : X} (hx : x ∈ F)
    (hc : ∀ q ∈ F, x * q = q * x) : x ∈ Subgroup.zpowers w :=
  h.cent x (h.le_cent hx) hc

theorem SevenLine.orderOf_w [Fact p.Prime] (h : SevenLine p w F) : orderOf w = p :=
  orderOf_eq_prime h.pow_eq h.ne_one

theorem SevenLine.comm_mem [Finite X] [Fact p.Prime] (h : SevenLine p w F) {v e : X} (hv : v ∈ F)
    (he : e ∈ F) : ∃ c ∈ Subgroup.zpowers w, v * e * v⁻¹ = e * c := by
  have hp := (Fact.out : p.Prime)
  have hzQ : w ∈ F := h.mem
  have hzcard : Nat.card (Subgroup.zpowers w) = p := by rw [Nat.card_zpowers, h.orderOf_w]
  have hzle : Subgroup.zpowers w ≤ F := (Subgroup.zpowers_le).2 hzQ
  set N : Subgroup ↥F := (Subgroup.zpowers w).subgroupOf F with hN'
  have hNnormal : N.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hcomm : (g : X) * (n : X) = (n : X) * (g : X) := by
      rw [← hk]
      have hcz : Commute w (g : X) := h.comm_w g.2
      exact (hcz.zpow_left k).eq.symm
    have e1 : (↑(g * n * g⁻¹) : X) = (n : X) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (g : X) * n * (g : X)⁻¹ = (n : X) * g * (g : X)⁻¹ := by rw [hcomm]
        _ = n := by group
    rw [e1]
    exact hn⟩
  have hNcard : Nat.card N = p := by
    rw [hN']
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzle).toEquiv, hzcard]
  have hquot : Nat.card (↥F ⧸ N) = p ^ 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [h.card_eq, hNcard] at h1
    have hp0 : 0 < p := hp.pos
    have : p ^ 3 = p ^ 2 * p := by ring
    rw [this] at h1
    exact (Nat.eq_of_mul_eq_mul_right hp0 h1).symm
  haveI := IsPGroup.isMulCommutative_of_card_eq_prime_sq hquot
  have hmk := mul_comm' (QuotientGroup.mk (⟨v, hv⟩ : ↥F) : ↥F ⧸ N) (QuotientGroup.mk ⟨e, he⟩)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul] at hmk
  have hmem := QuotientGroup.eq.1 hmk.symm
  rw [hN', Subgroup.mem_subgroupOf] at hmem
  set c : X := (e * v)⁻¹ * (v * e) with hcdef
  have hc_mem : c ∈ Subgroup.zpowers w := by
    have h1 : c = v⁻¹ * e⁻¹ * (v * e) := by rw [hcdef]; group
    rw [h1]
    simpa using hmem
  refine ⟨c, hc_mem, ?_⟩
  have hevc : v * e = e * v * c := by rw [hcdef]; group
  have hcv : v * c = c * v := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc_mem
    rw [← hk]
    have hcz : Commute w v := h.comm_w hv
    exact (hcz.zpow_left k).eq.symm
  calc v * e * v⁻¹ = (e * v * c) * v⁻¹ := by rw [hevc]
    _ = e * (v * c * v⁻¹) := by group
    _ = e * (c * v * v⁻¹) := by rw [hcv]
    _ = e * c := by group

theorem SevenLine.card_cent_le [Finite X] [Fact p.Prime] (h : SevenLine p w F) {e : X} (he : e ∈ F)
    (hew : e ∉ Subgroup.zpowers w) : Nat.card (F ⊓ Subgroup.centralizer ({e} : Set X) :
      Subgroup X) ≤ p ^ 2 := by
  have hp := (Fact.out : p.Prime)
  set D : Subgroup X := F ⊓ Subgroup.centralizer ({e} : Set X) with hD
  have hdvd : Nat.card D ∣ p ^ 3 := h.card_eq ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  by_contra hlt
  push Not at hlt
  have hj3 : j = 3 := by
    by_contra hne
    have : j ≤ 2 := by omega
    have : p ^ j ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos this
    omega
  have hDF : D = F := by
    refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
    rw [hj', hj3, h.card_eq]
  apply hew
  refine h.center_le he fun q hq => ?_
  have : q ∈ D := by rw [hDF]; exact hq
  exact (Subgroup.mem_centralizer_singleton_iff.1 this.2).symm

theorem SevenLine.fix_centralizer [Finite X] [Fact p.Prime] (h : SevenLine p w F) {e : X}
    (heF : e ∈ F) (hew : e ∉ Subgroup.zpowers w) (he7 : e ^ p = 1) {u : MulAut X}
    (hu : Nat.Coprime (orderOf u) p) (huw : u w = w) (hue : u e = e) :
    ∀ c ∈ Subgroup.centralizer ({w} : Set X), u c = c := by
  have hp := (Fact.out : p.Prime)
  have hfixZ : ∀ x ∈ Subgroup.zpowers w, u x = x := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [map_zpow, huw]
  have hC : ∀ c ∈ Subgroup.centralizer ({w} : Set X), u c ∈ Subgroup.centralizer ({w} : Set X) := by
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have := congrArg u hc
    rw [map_mul, map_mul, huw] at this
    exact this
  have hpow3 : ∀ f ∈ F, f ^ (p ^ 3) = 1 := by
    intro f hf
    have h1 : (⟨f, hf⟩ : F) ^ Nat.card F = 1 := pow_card_eq_one'
    rw [h.card_eq] at h1
    have := congrArg Subtype.val h1
    simpa using this
  have hF : ∀ f ∈ F, u f ∈ F := by
    intro f hf
    refine h.syl (u f) (hC f (h.le_cent hf)) ⟨3, ?_⟩
    rw [← map_pow, hpow3 f hf, map_one]
  have he1 : e ≠ 1 := fun h1 => hew (h1 ▸ Subgroup.one_mem _)
  have hcomm : Commute e w := (h.comm_w heF).symm
  have hwe : w ∉ Subgroup.zpowers e := by
    intro hw'
    have hle : Subgroup.zpowers w ≤ Subgroup.zpowers e := (Subgroup.zpowers_le).2 hw'
    have heq : Subgroup.zpowers w = Subgroup.zpowers e := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime he7 he1, h.orderOf_w]
    exact hew (heq ▸ Subgroup.mem_zpowers e)
  have hKcard := card_closure_pair_sq hcomm he7 h.pow_eq he1 hwe
  have heK : e ∈ Subgroup.closure ({e, w} : Set X) := Subgroup.subset_closure (by simp)
  have hwK : w ∈ Subgroup.closure ({e, w} : Set X) := Subgroup.subset_closure (by simp)
  have hKD : Subgroup.closure ({e, w} : Set X) ≤ F ⊓ Subgroup.centralizer ({e} : Set X) := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨heF, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
    · exact ⟨h.mem, Subgroup.mem_centralizer_singleton_iff.2 (h.comm_w heF)⟩
  have hKeq : Subgroup.closure ({e, w} : Set X) = F ⊓ Subgroup.centralizer ({e} : Set X) :=
    Subgroup.eq_of_le_of_card_ge hKD (by rw [hKcard]; exact h.card_cent_le heF hew)
  have hCe : ∀ t ∈ F ⊓ Subgroup.centralizer ({e} : Set X), u t = t := by
    intro t ht
    rw [← hKeq] at ht
    obtain ⟨i, -, j, -, rfl⟩ := exists_pow_mul_pow_of_mem hp.pos hcomm he7 h.pow_eq ht
    rw [map_mul, map_pow, map_pow, hue, huw]
  have hFfix : ∀ v ∈ F, u v = v := by
    intro v hv
    have hv' : u v ∈ F := hF v hv
    set t : X := v⁻¹ * u v with ht
    have htF : t ∈ F := mul_mem (inv_mem hv) hv'
    obtain ⟨c, hc, hvc⟩ := h.comm_mem hv heF
    have hcfix : u c = c := hfixZ c hc
    have h1 : u v * e * (u v)⁻¹ = v * e * v⁻¹ := by
      have := congrArg u hvc
      simp only [map_mul, map_inv, hue, hcfix] at this
      rw [this, hvc]
    have htC : t ∈ F ⊓ Subgroup.centralizer ({e} : Set X) := by
      refine ⟨htF, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      calc t * e = v⁻¹ * (u v * e * (u v)⁻¹) * u v := by rw [ht]; group
        _ = v⁻¹ * (v * e * v⁻¹) * u v := by rw [h1]
        _ = e * (v⁻¹ * u v) := by group
        _ = e * t := by rw [ht]
    have htfix : u t = t := hCe t htC
    have huv : u v = v * t := by rw [ht]; group
    have hiter : ∀ k : ℕ, (u ^ k) v = v * t ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, htfix, huv]
        group
    have hm : t ^ orderOf u = 1 := by
      have := hiter (orderOf u)
      rw [pow_orderOf_eq_one, MulAut.one_apply] at this
      exact mul_left_cancel (a := v) (by rw [mul_one]; exact this.symm)
    have ht1 : t = 1 := by
      have hd1 : orderOf t ∣ orderOf u := orderOf_dvd_of_pow_eq_one hm
      have hd2 : orderOf t ∣ p ^ 3 := orderOf_dvd_of_pow_eq_one (hpow3 t htF)
      have hcop : Nat.Coprime (orderOf u) (p ^ 3) := Nat.Coprime.pow_right 3 hu
      exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd1) hd2)
    rw [huv, ht1, mul_one]
  intro c hc
  have huc : u c ∈ Subgroup.centralizer ({w} : Set X) := hC c hc
  set s : X := c⁻¹ * u c with hs
  have hsC : s ∈ Subgroup.centralizer ({w} : Set X) := mul_mem (inv_mem hc) huc
  have hsF : ∀ f ∈ F, s * f = f * s := by
    intro f hf
    have hcf : c * f * c⁻¹ ∈ F := h.norm c hc f hf
    have h2 : u c * f * (u c)⁻¹ = c * f * c⁻¹ := by
      have := hFfix _ hcf
      rw [map_mul, map_mul, map_inv, hFfix f hf] at this
      exact this
    calc s * f = c⁻¹ * (u c * f * (u c)⁻¹) * u c := by rw [hs]; group
      _ = c⁻¹ * (c * f * c⁻¹) * u c := by rw [h2]
      _ = f * (c⁻¹ * u c) := by group
      _ = f * s := by rw [hs]
  have hsZ : s ∈ Subgroup.zpowers w := h.cent s hsC hsF
  have hsfix : u s = s := hfixZ s hsZ
  have hcs : u c = c * s := by rw [hs]; group
  have hiter : ∀ k : ℕ, (u ^ k) c = c * s ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hsfix, hcs]
      group
  have hm : s ^ orderOf u = 1 := by
    have := hiter (orderOf u)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at this
    exact mul_left_cancel (a := c) (by rw [mul_one]; exact this.symm)
  have hs1 : s = 1 := by
    have hd1 : orderOf s ∣ orderOf u := orderOf_dvd_of_pow_eq_one hm
    have hsp : s ^ p = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hsZ
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.pow_eq, one_zpow]
    have hd2 : orderOf s ∣ p := orderOf_dvd_of_pow_eq_one hsp
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hu.coprime_dvd_left hd1) hd2)
  rw [hcs, hs1, mul_one]

theorem exists_not_mem_zpowers_of_card [Finite X] [Fact p.Prime] {w : X} (hw : orderOf w = p)
    {E : Subgroup X} (hE2 : Nat.card E = p ^ 2) : ∃ e ∈ E, e ∉ Subgroup.zpowers w := by
  have hp := (Fact.out : p.Prime)
  by_contra hall
  push Not at hall
  have hle : E ≤ Subgroup.zpowers w := fun x hx => hall x hx
  have h1 := Subgroup.card_le_of_le hle
  rw [hE2, Nat.card_zpowers, hw] at h1
  have h2 : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

theorem SevenLine.mem_plane [Finite X] [Fact p.Prime] (h : SevenLine p w F) {E : Subgroup X}
    (hEF : E ≤ F) (hE2 : Nat.card E = p ^ 2) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    w ∈ E ∧ ∀ e ∈ E, e ∉ Subgroup.zpowers w → F ⊓ Subgroup.centralizer ({e} : Set X) = E := by
  obtain ⟨e, heE, hew⟩ := exists_not_mem_zpowers_of_card h.orderOf_w hE2
  have hEle : ∀ e' ∈ E, e' ∉ Subgroup.zpowers w →
      E ≤ F ⊓ Subgroup.centralizer ({e'} : Set X) := fun e' he' _ x hx =>
    ⟨hEF hx, Subgroup.mem_centralizer_singleton_iff.2 (hEc x hx e' he')⟩
  have hEeq : ∀ e' ∈ E, e' ∉ Subgroup.zpowers w →
      F ⊓ Subgroup.centralizer ({e'} : Set X) = E := fun e' he' hew' =>
    (Subgroup.eq_of_le_of_card_ge (hEle e' he' hew') (by
      rw [hE2]; exact h.card_cent_le (hEF he') hew')).symm
  refine ⟨?_, hEeq⟩
  have : w ∈ F ⊓ Subgroup.centralizer ({e} : Set X) :=
    ⟨h.mem, Subgroup.mem_centralizer_singleton_iff.2 (h.comm_w (hEF heE))⟩
  rw [hEeq e heE hew] at this
  exact this

theorem SevenLine.cent_plane_le [Finite X] [Fact p.Prime] (h : SevenLine p w F) {E : Subgroup X}
    (hEF : E ≤ F) (hE2 : Nat.card E = p ^ 2) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE7 : ∀ a ∈ E, a ^ p = 1) : ∀ c : X, (∀ s ∈ E, c * s = s * c) → c ∈ E := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨hwE, hDE⟩ := h.mem_plane hEF hE2 hEc
  obtain ⟨e, heE, hew⟩ := exists_not_mem_zpowers_of_card h.orderOf_w hE2
  intro c hc
  have hcw : c ∈ Subgroup.centralizer ({w} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hc w hwE)
  have hn0 : orderOf c ≠ 0 := (orderOf_pos c).ne'
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hp.ne_one
  set c' : X := c ^ (p ^ a) with hc'
  have hc'b : c' ^ b = 1 := by
    rw [hc', ← pow_mul, ← hab, pow_orderOf_eq_one]
  have hc'cop : Nat.Coprime (orderOf c') p := by
    have hd : orderOf c' ∣ b := orderOf_dvd_of_pow_eq_one hc'b
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hb).symm.coprime_dvd_left hd
  have hc'comm : ∀ s ∈ E, c' * s = s * c' := by
    intro s hs
    exact (Commute.pow_left (show Commute c s from hc s hs) (p ^ a)).eq
  have hc'cop' : Nat.Coprime (orderOf (MulAut.conj c' : MulAut X)) p :=
    Nat.Coprime.coprime_dvd_left (orderOf_map_dvd (MulAut.conj : X →* MulAut X) c') hc'cop
  have hc'w : (MulAut.conj c' : MulAut X) w = w := by
    rw [MulAut.conj_apply]
    calc c' * w * c'⁻¹ = w * c' * c'⁻¹ := by rw [hc'comm w hwE]
      _ = w := by group
  have hc'e : (MulAut.conj c' : MulAut X) e = e := by
    rw [MulAut.conj_apply]
    calc c' * e * c'⁻¹ = e * c' * c'⁻¹ := by rw [hc'comm e heE]
      _ = e := by group
  have hfix := h.fix_centralizer (hEF heE) hew (hE7 e heE) hc'cop' hc'w hc'e
  have hc'C : c' ∈ Subgroup.centralizer ({w} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hc'comm w hwE)
  have hc'Z : c' ∈ Subgroup.zpowers w := by
    refine h.cent c' hc'C fun f hf => ?_
    have := hfix f (h.le_cent hf)
    rw [MulAut.conj_apply] at this
    calc c' * f = c' * f * c'⁻¹ * c' := by group
      _ = f * c' := by rw [this]
  have hc'1 : c' = 1 := by
    have hsp : c' ^ p = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc'Z
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.pow_eq, one_zpow]
    have hd1 : orderOf c' ∣ p := orderOf_dvd_of_pow_eq_one hsp
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hc'cop hd1)
  have hcp : c ^ (p ^ a) = 1 := hc'1
  have hcF : c ∈ F := h.syl c hcw ⟨a, hcp⟩
  have : c ∈ F ⊓ Subgroup.centralizer ({e} : Set X) :=
    ⟨hcF, Subgroup.mem_centralizer_singleton_iff.2 (hc e heE)⟩
  rw [hDE e heE hew] at this
  exact this

end Line

section Normalizer

variable {X : Type*} [Group X] {p : ℕ}

theorem fix_of_normalizes [Finite X] {u : MulAut X} {p : ℕ} [Fact p.Prime]
    (hu : Nat.Coprime (orderOf u) p) {S : Subgroup X} (hSfix : ∀ s ∈ S, u s = s)
    (hSp : ∀ s ∈ S, ∃ n : ℕ, s ^ (p ^ n) = 1)
    (hCS : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c ∈ S) {g : X}
    (hg : ∀ s ∈ S, g * s * g⁻¹ ∈ S) : u g = g := by
  set t : X := g⁻¹ * u g with ht
  have htC : ∀ s ∈ S, t * s = s * t := by
    intro s hs
    have h1 : u g * s * (u g)⁻¹ = g * s * g⁻¹ := by
      have := hSfix _ (hg s hs)
      simp only [map_mul, map_inv, hSfix s hs] at this
      exact this
    calc t * s = g⁻¹ * (u g * s * (u g)⁻¹) * u g := by rw [ht]; group
      _ = g⁻¹ * (g * s * g⁻¹) * u g := by rw [h1]
      _ = s * (g⁻¹ * u g) := by group
      _ = s * t := by rw [ht]
  have htS : t ∈ S := hCS t htC
  have htfix : u t = t := hSfix t htS
  have hug : u g = g * t := by rw [ht]; group
  have hiter : ∀ k : ℕ, (u ^ k) g = g * t ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, htfix, hug]
      group
  have hm : t ^ orderOf u = 1 := by
    have := hiter (orderOf u)
    rw [pow_orderOf_eq_one, MulAut.one_apply] at this
    exact mul_left_cancel (a := g) (by rw [mul_one]; exact this.symm)
  have ht1 : t = 1 := by
    obtain ⟨n, hn⟩ := hSp t htS
    have hd1 : orderOf t ∣ orderOf u := orderOf_dvd_of_pow_eq_one hm
    have hd2 : orderOf t ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn
    have hcop : Nat.Coprime (orderOf u) (p ^ n) := Nat.Coprime.pow_right n hu
    exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd (hcop.coprime_dvd_left hd1) hd2)
  rw [hug, ht1, mul_one]

end Normalizer

section Model

variable {X : Type*} [Group X] {p : ℕ}

structure SevenModel (X : Type*) [Group X] (p : ℕ) (Q : Subgroup X) (z : X) (gens : Set X) :
    Prop where
  line : SevenLine p z Q
  syl : ∃ S : Sylow p X, (S : Subgroup X) = Q
  gens_top : Subgroup.closure gens = ⊤
  gens_good : ∀ g ∈ gens, g ∈ Subgroup.centralizer ({z} : Set X) ∨
    (∃ (w : X) (F : Subgroup X), SevenLine p w F ∧ w ∈ Q ∧ w ∉ Subgroup.zpowers z ∧
      g ∈ Subgroup.centralizer ({w} : Set X)) ∨
    (∃ E : Subgroup X, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      ∀ s ∈ E, g * s * g⁻¹ ∈ E)
  rankOK : ∀ e : X, orderOf e = p → RankOK p (Subgroup.centralizer ({e} : Set X))

theorem mem_zpowers_symm [Finite X] [Fact p.Prime] {z w : X} (hz : orderOf z = p)
    (hw : orderOf w = p) (h : z ∈ Subgroup.zpowers w) : w ∈ Subgroup.zpowers z := by
  have hle : Subgroup.zpowers z ≤ Subgroup.zpowers w := (Subgroup.zpowers_le).2 h
  have heq : Subgroup.zpowers z = Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hz, hw])
  exact heq ▸ Subgroup.mem_zpowers w

theorem SevenModel.fix_plane [Finite X] [Fact p.Prime] {Q : Subgroup X} {z : X} {gens : Set X}
    (D : SevenModel X p Q z gens) {E : Subgroup X} (hEQ : E ≤ Q) (hEel : IsElemAbelian p E)
    (hE2 : Nat.card E = p ^ 2) {u : MulAut X} (hu : Nat.Coprime (orderOf u) p)
    (hEfix : ∀ s ∈ E, u s = s) : u = 1 := by
  have hp := (Fact.out : p.Prime)
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hE7 : ∀ a ∈ E, a ^ p = 1 := hEel.2
  have hz := D.line
  obtain ⟨hzE, -⟩ := hz.mem_plane hEQ hE2 hEc
  obtain ⟨e, heE, hez⟩ := exists_not_mem_zpowers_of_card hz.orderOf_w hE2
  have huz : u z = z := hEfix z hzE
  have hCz : ∀ c ∈ Subgroup.centralizer ({z} : Set X), u c = c :=
    hz.fix_centralizer (hEQ heE) hez (hE7 e heE) hu huz (hEfix e heE)
  have hQfix : ∀ q ∈ Q, u q = q := fun q hq => hCz q (hz.le_cent hq)
  have hgens : ∀ g ∈ gens, u g = g := by
    intro g hg
    rcases D.gens_good g hg with h1 | ⟨w, F, hw, hwQ, hwz, h2⟩ | ⟨E', hE'Q, hE'el, hE'2, hE'n⟩
    · exact hCz g h1
    · have hzw : z ∉ Subgroup.zpowers w := fun h' =>
        hwz (mem_zpowers_symm hz.orderOf_w hw.orderOf_w h')
      have hzC : z ∈ Subgroup.centralizer ({w} : Set X) :=
        Subgroup.mem_centralizer_singleton_iff.2 (hz.comm_w hwQ)
      have hzF : z ∈ F := hw.syl z hzC ⟨1, by rw [pow_one]; exact hz.pow_eq⟩
      exact hw.fix_centralizer hzF hzw hz.pow_eq hu (hQfix w hwQ) huz g h2
    · have hE'c : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := fun a ha b hb =>
        congrArg Subtype.val (hE'el.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
      refine fix_of_normalizes hu (S := E') (fun s hs => hQfix s (hE'Q hs)) ?_
        (hz.cent_plane_le hE'Q hE'2 hE'c hE'el.2) hE'n
      intro s hs
      exact ⟨1, by rw [pow_one]; exact hE'el.2 s hs⟩
  ext x
  have hx : x ∈ Subgroup.closure gens := by rw [D.gens_top]; exact Subgroup.mem_top x
  rw [MulAut.one_apply]
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hgens y hy
  | one => exact map_one u
  | mul y z' _ _ hy hz' => rw [map_mul, hy, hz']
  | inv y _ hy => rw [map_inv, hy]

theorem SevenModel.noSig [Finite X] [Fact p.Prime] (hp2 : p ≠ 2) {Q : Subgroup X} {z : X}
    {gens : Set X} (D : SevenModel X p Q z gens) (hcen : Subgroup.center X = ⊥)
    (hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ≤ 2) :
    ∀ Ê : Subgroup (MulAut X), IsElemAbelian p Ê → Nat.card Ê = p ^ 2 → NoSig p Ê :=
  noSig_planes_of_sylow (Fact.out : p.Prime) hp2 hcen hout D.syl fun E₀ hE₀Q hEel hE2 =>
    noSig_of_inner_outer (Fact.out : p.Prime) hp2 hcen hout hEel hE2
      (fun e he he1 => D.rankOK e (orderOf_eq_prime (hEel.2 e he) he1))
      (fun σ hσ hfix => D.fix_plane hE₀Q hEel hE2 hσ hfix)

end Model

section FromData

variable {X : Type*} [Group X] [Finite X]

theorem sevenLine_of_data {p : ℕ} [Fact p.Prime] {w : X} {F : Subgroup X} {m : ℕ}
    (hw1 : w ≠ 1) (hw7 : w ^ p = 1) (hwF : w ∈ F)
    (hC : Nat.card (Subgroup.centralizer ({w} : Set X)) = p ^ 3 * m) (hm : ¬ p ∣ m)
    (hFC : F ≤ Subgroup.centralizer ({w} : Set X)) (hFcard : Nat.card F = p ^ 3)
    (hFn : ∀ c ∈ Subgroup.centralizer ({w} : Set X), ∀ f ∈ F, c * f * c⁻¹ ∈ F)
    (hFcent : ∀ c ∈ Subgroup.centralizer ({w} : Set X), (∀ f ∈ F, c * f = f * c) →
      c ∈ Subgroup.zpowers w) : SevenLine p w F := by
  have hp := (Fact.out : p.Prime)
  refine ⟨hw1, hw7, hwF, hFC, hFcard, ?_, hFn, hFcent⟩
  intro c hc ⟨n, hn⟩
  set C := Subgroup.centralizer ({w} : Set X) with hCdef
  have hfac : (Nat.card C).factorization p = 3 := by
    rw [hC, Nat.factorization_mul (pow_ne_zero 3 hp.ne_zero) (by
      rintro rfl; exact hm (dvd_zero p)), Finsupp.add_apply, hp.factorization_pow,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm, add_zero]
  set S : Subgroup C := F.subgroupOf C with hS
  have hScard : Nat.card S = p ^ (Nat.card C).factorization p := by
    rw [hfac, hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFC).toEquiv, hFcard]
  let P : Sylow p C := Sylow.ofCard S hScard
  have hPnorm : P.Normal := ⟨fun x hx g => by
    have hx' : (x : C) ∈ S := hx
    rw [hS, Subgroup.mem_subgroupOf] at hx'
    show g * x * g⁻¹ ∈ S
    rw [hS, Subgroup.mem_subgroupOf]
    have := hFn g g.2 x hx'
    simpa using this⟩
  haveI : Finite (Sylow p C) := inferInstance
  set c' : C := ⟨c, hc⟩ with hc'
  have hcyc : IsPGroup p (Subgroup.zpowers c') := by
    have hn' : c' ^ (p ^ n) = 1 := Subtype.ext (by simpa using hn)
    have hord : orderOf c' ∣ p ^ n := orderOf_dvd_of_pow_eq_one hn'
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 hord
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨S', hS'⟩ := hcyc.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C P S'
  have hS'eq : S' = P := by
    rw [← hg, Sylow.smul_eq_of_normal]
  have hc'S : c' ∈ (P : Subgroup C) := by
    rw [← hS'eq]
    exact hS' (Subgroup.mem_zpowers c')
  have : c' ∈ S := hc'S
  rw [hS, Subgroup.mem_subgroupOf] at this
  exact this

end FromData

end CFSG.HardMathSupport.Dickson.I271
