module

public import CFSG.CGT.Foote82.Lemma62Core
import CFSG.Quasithin.Background.G11Basic

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11
open scoped commutatorElement

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {G L K : Subgroup (GLV V)} {s : GLV V} {p : ℕ}

private theorem mem_normalizer_of_conj_mem {M : Subgroup (GLV V)} {g : GLV V}
    (h1 : ∀ m ∈ M, g * m * g⁻¹ ∈ M) (h2 : ∀ m ∈ M, g⁻¹ * m * g ∈ M) :
    g ∈ Subgroup.normalizer (M : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro m
  refine ⟨h1 m, fun hm => ?_⟩
  simpa [mul_assoc] using h2 _ hm

private theorem zpowers_conj_mem {g d : GLV V} (h : g * d = d * g) :
    ∀ b ∈ Subgroup.zpowers d, g * b * g⁻¹ ∈ Subgroup.zpowers d := by
  intro b hb
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have : g * d ^ n * g⁻¹ = d ^ n := by
    rw [(Commute.zpow_right (show Commute g d from h) n).eq]
    group
  rw [this]
  exact Subgroup.zpow_mem_zpowers d n

private theorem Core62.perfect (hc : Core62 G L K s p) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 hc.conf.setup.component.2.2.1)

private theorem Core62.sq (hc : Core62 G L K s p) : s ^ 2 = 1 := by
  have h := pow_orderOf_eq_one s
  rwa [hc.s_ord] at h

private theorem Core62.inv_s (hc : Core62 G L K s p) : s⁻¹ = s :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_two, hc.sq])

private theorem Core62.s_conj_mem (hc : Core62 G L K s p) : ∀ k ∈ K, s * k * s⁻¹ ∈ K := fun k hk =>
  (Subgroup.mem_normalizer_iff.1 (hc.conf.S_le (Subgroup.mem_zpowers s)) k).1 hk

private theorem Core62.L_conj_mem (hc : Core62 G L K s p) : ∀ l ∈ L, ∀ k ∈ K, l * k * l⁻¹ ∈ K :=
  fun l hl k hk => (Subgroup.mem_normalizer_iff.1 (hc.conf.L_le hl) k).1 hk

private theorem Core62.L_comm (hc : Core62 G L K s p) : ∀ l ∈ L, l * s = s * l := by
  intro l hl
  have hLC : L ≤ G ⊓ Subgroup.centralizer ((Subgroup.zpowers s : Subgroup (GLV V)) : Set (GLV V)) :=
    hc.conf.setup.component.1
  exact ((Subgroup.mem_centralizer_iff.1 (hLC hl).2) s (Subgroup.mem_zpowers s)).symm

private theorem Core62.frat_comm (hc : Core62 G L K s p) :
    ∀ d ∈ frat K, ∀ k ∈ K, k * d = d * k := fun d hd k hk =>
  Subgroup.mem_centralizer_iff.1 (hc.frat_center hd) k hk

private theorem Core62.frat_comm_L (hc : Core62 G L K s p) :
    ∀ d ∈ frat K, ∀ l ∈ L, l * d = d * l := fun d hd l hl =>
  Subgroup.mem_centralizer_iff.1 (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc.frat_L hd) l hl

private theorem Core62.bot_lt_top (hc : Core62 G L K s p) : (⊥ : Submodule (ZMod 2) V) < ⊤ :=
  lt_of_le_of_lt bot_le (lt_of_lt_of_le hc.conf.setup.irrTilde.1 le_top)

private theorem Core62.odd_of_le (hc : Core62 G L K s p) {B : Subgroup (GLV V)} (h : B ≤ K) :
    Odd (Nat.card B) :=
  Odd.of_dvd_nat hc.conf.odd (Subgroup.card_dvd_of_le h)

private theorem Core62.dichotomy (hc : Core62 G L K s p) {B : Subgroup (GLV V)}
    (hB : Odd (Nat.card B)) (hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B)
    (hLB : ∀ l ∈ L, ∀ b ∈ B, l * b * l⁻¹ ∈ B) : fixedSpace B = ⊥ ∨ B = ⊥ := by
  have hcompl := isCompl_fixedSpace_commSpace hB
  have hKmem : ∀ k ∈ K, k ∈ ⁅K, L⁆ := fun k hk => by rw [hc.KL]; exact hk
  rcases trivial_on_summand hc.perfect hc.conf.setup.irrTilde hcompl
    (invariant_fixedSpace hLB) (invariant_commSpace hLB (invariant_top L)) with h | h
  · left
    rw [eq_bot_iff, ← hc.fix]
    intro x hx k hk
    exact fixes_of_commutator (invariant_fixedSpace hKB) h k (hKmem k hk) x hx
  · right
    have hle : commSpace B ⊤ ≤ fixedSpace K := fun x hx k hk =>
      fixes_of_commutator (invariant_commSpace hKB (invariant_top K)) h k (hKmem k hk) x hx
    rw [hc.fix, le_bot_iff, commSpace_eq_bot_iff] at hle
    rw [Subgroup.eq_bot_iff_forall]
    intro b hb
    exact LinearEquiv.ext fun v => hle b hb v Submodule.mem_top

private theorem Core62.s_centralizes_center (hc : Core62 G L K s p) :
    ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set (GLV V)) → s * z * s⁻¹ = z := by
  have hs2 := hc.sq
  have hsinv := hc.inv_s
  have hsZ : ∀ z ∈ K, z ∈ Subgroup.centralizer (K : Set (GLV V)) →
      s * z * s⁻¹ ∈ Subgroup.centralizer (K : Set (GLV V)) := by
    intro z hzK hzC
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : s⁻¹ * k * s ∈ K := by
      have := hc.s_conj_mem k hk
      rwa [hsinv] at this ⊢
    have h2 := Subgroup.mem_centralizer_iff.1 hzC _ h1
    calc k * (s * z * s⁻¹) = s * ((s⁻¹ * k * s) * z) * s⁻¹ := by group
      _ = s * (z * (s⁻¹ * k * s)) * s⁻¹ := by rw [h2]
      _ = (s * z * s⁻¹) * k := by group
  let B : Subgroup (GLV V) :=
    { carrier := {z | z ∈ K ∧ z ∈ Subgroup.centralizer (K : Set (GLV V)) ∧ s * z * s⁻¹ = z⁻¹}
      mul_mem' := by
        rintro a b ⟨haK, haC, has⟩ ⟨hbK, hbC, hbs⟩
        refine ⟨K.mul_mem haK hbK, Subgroup.mul_mem _ haC hbC, ?_⟩
        have hab : a * b = b * a := (Subgroup.mem_centralizer_iff.1 haC b hbK).symm
        calc s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [has, hbs]
          _ = (a * b)⁻¹ := by rw [hab, mul_inv_rev]
      one_mem' := ⟨K.one_mem, Subgroup.one_mem _, by group⟩
      inv_mem' := by
        rintro a ⟨haK, haC, has⟩
        refine ⟨K.inv_mem haK, Subgroup.inv_mem _ haC, ?_⟩
        calc s * a⁻¹ * s⁻¹ = (s * a * s⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [has] }
  have hBK : B ≤ K := fun z hz => hz.1
  have hBodd : Odd (Nat.card B) := hc.odd_of_le hBK
  have hab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.1 ha.2.1 b hb.1).symm
  have hinv : ∀ b ∈ B, s * b * s⁻¹ = b⁻¹ := fun b hb => hb.2.2
  have hKB : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ ∈ B := by
    intro k hk b hb
    have : k * b * k⁻¹ = b := by
      rw [Subgroup.mem_centralizer_iff.1 hb.2.1 k hk]
      group
    rw [this]
    exact hb
  have hLB : ∀ l ∈ L, ∀ b ∈ B, l * b * l⁻¹ ∈ B := by
    intro l hl b hb
    obtain ⟨hbK, hbC, hbs⟩ := hb
    have hls : s * l * s⁻¹ = l := by
      rw [← hc.L_comm l hl]
      group
    refine ⟨hc.L_conj_mem l hl b hbK, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h1 : l⁻¹ * k * l ∈ K := by
        have := hc.L_conj_mem l⁻¹ (L.inv_mem hl) k hk
        simpa using this
      have h2 := Subgroup.mem_centralizer_iff.1 hbC _ h1
      calc k * (l * b * l⁻¹) = l * ((l⁻¹ * k * l) * b) * l⁻¹ := by group
        _ = l * (b * (l⁻¹ * k * l)) * l⁻¹ := by rw [h2]
        _ = (l * b * l⁻¹) * k := by group
    · calc s * (l * b * l⁻¹) * s⁻¹ = (s * l * s⁻¹) * (s * b * s⁻¹) * (s * l * s⁻¹)⁻¹ := by group
        _ = l * b⁻¹ * l⁻¹ := by rw [hls, hbs]
        _ = (l * b * l⁻¹)⁻¹ := by group
  have hBbot : B = ⊥ := by
    rcases hc.dichotomy hBodd hKB hLB with hfix | hbot
    · exact (Setup6.false_of_inverts hc.conf.setup (Subgroup.mem_zpowers s) hs2 hBodd hab hinv
        hfix).elim
    · exact hbot
  intro z hzK hzC
  have hy : s * z * s⁻¹ * z⁻¹ ∈ B := by
    have hsz : s * z * s⁻¹ ∈ K := hc.s_conj_mem z hzK
    refine ⟨K.mul_mem hsz (K.inv_mem hzK), Subgroup.mul_mem _ (hsZ z hzK hzC)
      (Subgroup.inv_mem _ hzC), ?_⟩
    have hss : s * s = 1 := by rw [← pow_two, hs2]
    calc s * (s * z * s⁻¹ * z⁻¹) * s⁻¹ = (s * s) * z * s⁻¹ * z⁻¹ * s⁻¹ := by group
      _ = z * s⁻¹ * z⁻¹ * s⁻¹ := by rw [hss, one_mul]
      _ = z * s * z⁻¹ * s⁻¹ := by rw [hsinv]
      _ = (s * z * s⁻¹ * z⁻¹)⁻¹ := by group
  rw [hBbot, Subgroup.mem_bot] at hy
  exact mul_inv_eq_one.1 hy

theorem Core62.center_le_frat (hc : Core62 G L K s p) :
    K ⊓ Subgroup.centralizer (K : Set (GLV V)) ≤ frat K := by
  intro z hz
  obtain ⟨hzK, hzC⟩ := hz
  have h2 := hc.inverts z hzK
  rw [hc.s_centralizes_center z hzK hzC] at h2
  have hodd : Odd (orderOf z) := by
    have h : orderOf (⟨z, hzK⟩ : K) ∣ Nat.card K := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd_nat hc.conf.odd h
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 2) (Nat.coprime_two_left.2 hodd)
  have hz2 : z ^ 2 ∈ frat K := by rwa [pow_two]
  have := Subgroup.pow_mem (frat K) hz2 m
  rwa [hm] at this

theorem Core62.irreducible (hc : Core62 G L K s p) :
    ∀ M : Subgroup (GLV V), frat K ≤ M → M ≤ K → L ≤ Subgroup.normalizer (M : Set (GLV V)) →
      M = frat K ∨ M = K := by
  intro M hFM hMK hLM
  haveI := Fact.mk hc.prime
  by_cases hMK' : M = K
  · exact Or.inr hMK'
  refine Or.inl ?_
  have hlt : M < K := lt_of_le_of_ne hMK hMK'
  have hKM : ∀ k ∈ K, ∀ m ∈ M, k * m * k⁻¹ ∈ M := by
    intro k hk m hm
    have h1 : ⁅k, m⁆ ∈ frat K :=
      commutator_le_frat hc.pgroup (Subgroup.commutator_mem_commutator hk (hMK hm))
    have h2 : k * m * k⁻¹ = ⁅k, m⁆ * m := by simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact M.mul_mem (hFM h1) hm
  have hsM : ∀ m ∈ M, s * m * s⁻¹ ∈ M := by
    intro m hm
    have h1 : s * m * s⁻¹ * m ∈ frat K := hc.inverts m (hMK hm)
    have h2 : s * m * s⁻¹ = (s * m * s⁻¹ * m) * m⁻¹ := by group
    rw [h2]
    exact M.mul_mem (hFM h1) (M.inv_mem hm)
  have hsnorm : Subgroup.zpowers s ≤ Subgroup.normalizer (M : Set (GLV V)) := by
    rw [Subgroup.zpowers_le]
    refine mem_normalizer_of_conj_mem hsM fun m hm => ?_
    rw [hc.inv_s]
    simpa [hc.inv_s] using hsM m hm
  have hML : ⁅M, L⁆ = ⊥ := hc.min M hlt hsnorm hLM
  have hMK_le : ⁅M, K⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro m hm k hk
    have h : ⁅m, k⁆ = m * (k * m⁻¹ * k⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [h]
    exact M.mul_mem hm (hKM k hk m⁻¹ (M.inv_mem hm))
  have h3 : ⁅⁅K, L⁆, M⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [Subgroup.commutator_comm L M, hML, Subgroup.commutator_bot_left]
    · rw [eq_bot_iff, ← hML]
      exact Subgroup.commutator_mono hMK_le le_rfl
  rw [hc.KL, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  exact le_antisymm (fun m hm => hc.center_le_frat ⟨hMK hm, h3 hm⟩) hFM

theorem Core62.pow_eq_one (hc : Core62 G L K s p) : ∀ k ∈ K, k ^ p = 1 := by
  haveI := Fact.mk hc.prime
  have hcomm : ∀ x ∈ K, ∀ y ∈ K, ⁅y, x⁆ ∈ frat K := fun x hx y hy =>
    commutator_le_frat hc.pgroup (Subgroup.commutator_mem_commutator hy hx)
  have hmul : ∀ x ∈ K, ∀ y ∈ K, (x * y) ^ p = x ^ p * y ^ p := by
    intro x hx y hy
    have hxc : Commute x ⁅y, x⁆ := hc.frat_comm _ (hcomm x hx y hy) x hx
    have hyc : Commute y ⁅y, x⁆ := hc.frat_comm _ (hcomm x hx y hy) y hy
    have hcp : ⁅y, x⁆ ^ p = 1 := by
      rw [hxc.commutatorElement_pow_right]
      exact Commute.commutator_eq (hc.frat_comm _ (pow_mem_frat hc.pgroup hx) y hy)
    have hdvd : p ∣ p.choose 2 :=
      hc.prime.dvd_choose_self (by norm_num) (by have := hc.prime.two_le; have := hc.p_ne; omega)
    obtain ⟨m, hm⟩ := hdvd
    rw [Commute.mul_pow_eq_pow_mul_pow_mul_commutatorElement_pow_choose_two hxc hyc, hm,
      pow_mul, hcp, one_pow, mul_one]
  let S : Subgroup (GLV V) :=
    { carrier := {k | k ∈ K ∧ k ^ p = 1}
      mul_mem' := fun {a b} ha hb =>
        ⟨K.mul_mem ha.1 hb.1, by rw [hmul a ha.1 b hb.1, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨K.one_mem, one_pow p⟩
      inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hKS : ⁅K, L⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hlx : l * x * l⁻¹ ∈ K := hc.L_conj_mem l hl x hx
    have hxl : ⁅x, l⁆ = x * (l * x * l⁻¹)⁻¹ := by simp [commutatorElement_def, mul_assoc]
    have hxp : x ^ p ∈ frat K := pow_mem_frat hc.pgroup hx
    have hlxp : l * x ^ p * l⁻¹ = x ^ p := by
      rw [hc.frat_comm_L _ hxp l hl]
      group
    refine ⟨by rw [hxl]; exact K.mul_mem hx (K.inv_mem hlx), ?_⟩
    show ⁅x, l⁆ ^ p = 1
    rw [hxl, hmul x hx _ (K.inv_mem hlx), inv_pow, conj_pow, hlxp, mul_inv_cancel]
  rw [hc.KL] at hKS
  exact fun k hk => (hKS hk).2

theorem Core62.frat_eq_center (hc : Core62 G L K s p) :
    frat K = K ⊓ Subgroup.centralizer (K : Set (GLV V)) :=
  le_antisymm (le_inf (frat_le K) hc.frat_center) hc.center_le_frat

theorem Core62.frat_eq_commutator (hc : Core62 G L K s p) : frat K = ⁅K, K⁆ := by
  haveI := Fact.mk hc.prime
  haveI : Fact (IsPGroup p ↥K) := ⟨hc.pgroup⟩
  refine le_antisymm ?_ (commutator_le_frat hc.pgroup)
  have hle : frattini ↥K ≤ _root_.commutator ↥K := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (R := ↥K) (p := p), Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · exact hx
    · have hy : y ^ p = 1 := Subtype.ext (by simpa using hc.pow_eq_one y y.2)
      show y ^ p ∈ _root_.commutator ↥K
      rw [hy]
      exact (_root_.commutator ↥K).one_mem
  calc frat K = (frattini ↥K).map K.subtype := rfl
    _ ≤ (_root_.commutator ↥K).map K.subtype := Subgroup.map_mono hle
    _ = ⁅K, K⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]

theorem Core62.s_centralizes_frat (hc : Core62 G L K s p) :
    ∀ d ∈ frat K, s * d * s⁻¹ = d := fun d hd =>
  hc.s_centralizes_center d (frat_le K hd) (hc.frat_center hd)

theorem Core62.fixedSpace_eq_bot_of_mem_frat (hc : Core62 G L K s p) :
    ∀ d ∈ frat K, d ≠ 1 → fixedSpace (Subgroup.zpowers d) = ⊥ := by
  intro d hd hd1
  have hodd : Odd (Nat.card (Subgroup.zpowers d)) :=
    hc.odd_of_le (Subgroup.zpowers_le.2 (frat_le K hd))
  rcases hc.dichotomy hodd (fun k hk => zpowers_conj_mem (hc.frat_comm d hd k hk))
    (fun l hl => zpowers_conj_mem (hc.frat_comm_L d hd l hl)) with h | h
  · exact h
  · exact absurd (Subgroup.zpowers_eq_bot.1 h) hd1

theorem Core62.card_frat (hc : Core62 G L K s p) : Nat.card (frat K) = p := by
  haveI := Fact.mk hc.prime
  have hVne := hc.bot_lt_top
  have hKbot : K ≠ ⊥ := by
    intro hK
    have h1 : fixedSpace K = ⊤ :=
      fixedSpace_eq_top_iff.2 fun k hk => by rw [hK] at hk; exact Subgroup.mem_bot.1 hk
    rw [hc.fix] at h1
    exact hVne.ne h1
  have hFne : frat K ≠ ⊥ := by
    intro hF
    haveI : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hKbot
    haveI : Nontrivial ↥(Subgroup.center ↥K) := hc.pgroup.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : ↥(Subgroup.center ↥K))
    have hzC : ((z : ↥K) : GLV V) ∈ Subgroup.centralizer (K : Set (GLV V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩)
    have hz := hc.center_le_frat ⟨(z : ↥K).2, hzC⟩
    rw [hF, Subgroup.mem_bot] at hz
    exact hz1 (Subtype.ext (Subtype.ext hz))
  obtain ⟨n, hn⟩ := (hc.pgroup.to_le (frat_le K)).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hFne (Subgroup.eq_bot_of_card_eq _ (by simpa using hn))
  have hn1 : n < 2 := by
    by_contra hcon
    obtain ⟨E, hEcard, -, hEle⟩ := Sylow.exists_subgroup_card_pow_prime_le_le (G := GLV V)
      (p := p) (n := 2) (H := ⊥) (L := frat K) hc.prime
      (by rw [Subgroup.card_bot]; exact one_dvd _)
      (by rw [hn]; exact pow_dvd_pow p (not_lt.1 hcon)) bot_le
    have hab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      hc.frat_comm b (hEle hb) a (frat_le K (hEle ha))
    have hexp : ∀ e ∈ E, e ^ p = 1 := fun e he => hc.pow_eq_one e (frat_le K (hEle he))
    have hsup := iSup_fixedSpace_eq_top hc.prime hc.p_ne hab hexp hEcard
    have hbot : (⨆ (H : Subgroup (GLV V)) (_ : H ≤ E) (_ : Nat.card H = p), fixedSpace H) = ⊥ := by
      refine iSup_eq_bot.2 fun H => iSup_eq_bot.2 fun hHE => iSup_eq_bot.2 fun hHp => ?_
      have hHne : H ≠ ⊥ := by
        intro hH
        rw [hH, Subgroup.card_bot] at hHp
        exact hc.prime.one_lt.ne hHp
      obtain ⟨⟨h, hhH⟩, hh1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hHne
      have hfix := hc.fixedSpace_eq_bot_of_mem_frat h (hEle (hHE hhH))
        (fun h' => hh1 (Subtype.ext h'))
      exact le_bot_iff.1 ((fixedSpace_anti (Subgroup.zpowers_le.2 hhH)).trans hfix.le)
    rw [hbot] at hsup
    exact hVne.ne hsup
  have hn' : n = 1 := by omega
  rw [hn, hn', pow_one]

end CFSG.CGT.Foote82
