module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264RowData
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabCo1Gen
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264SporAll
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

theorem false_of_pConstrainedShape_of_normal_simple {Q : Type} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) {C L : Subgroup Q} (hLC : L ≤ C) (hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L)
    (hs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (h : CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PConstrainedShape p C) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, hRC, hRn, hRp, hcR⟩ := h
  have hLR : L ≤ R := by
    have hN : (R.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hRn g (hLC g.2) n hn⟩
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf L) with hbot | htop
    · intro l hl
      refine hcR ⟨hLC hl, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
      have h1 : l * r * l⁻¹ * r⁻¹ ∈ L := by
        have := hLn r (hRC hr) l⁻¹ (L.inv_mem hl)
        have h2 : l * r * l⁻¹ * r⁻¹ = l * (r * l⁻¹ * r⁻¹) := by group
        rw [h2]
        exact L.mul_mem hl this
      have h2 : l * r * l⁻¹ * r⁻¹ ∈ R := R.mul_mem (hRn l (hLC hl) r hr) (R.inv_mem hr)
      have h3 : (⟨_, h1⟩ : ↥L) ∈ R.subgroupOf L := Subgroup.mem_subgroupOf.2 h2
      rw [hbot, Subgroup.mem_bot] at h3
      have h4 : l * r * l⁻¹ * r⁻¹ = 1 := congrArg Subtype.val h3
      calc r * l = (l * r * l⁻¹ * r⁻¹)⁻¹ * (l * r) := by group
        _ = l * r := by rw [h4, inv_one, one_mul]
    · intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ R.subgroupOf L := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
  have hLp : IsPGroup p ↥L := hRp.to_le hLR
  obtain ⟨a, b, hab⟩ := hnab
  haveI : Nontrivial ↥L := ⟨⟨a * b, b * a, hab⟩⟩
  have hZ := hLp.center_nontrivial
  have hZtop : Subgroup.center ↥L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with h | h
    · exfalso
      obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center ↥L)
      rw [h, Subgroup.mem_bot] at hz
      exact hz1 (Subtype.ext hz)
    · exact h
  exact hab ((Subgroup.mem_center_iff.1 (hZtop ▸ Subgroup.mem_top b)) a)

theorem exists_glaPComponent_of_bound {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {x : Q} (hx1 : x ≠ 1) (hxp : x ^ p = 1) {L : Subgroup Q}
    (hLC : L ≤ Subgroup.centralizer ({x} : Set Q)) (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (hbound : Nat.card ↥(Subgroup.centralizer ({x} : Set Q)) ≤ p * Nat.card ↥L) :
    ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) J := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set Q) with hC
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcomm : ∀ l ∈ L, l * x = x * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
  have hZ : ∀ l ∈ L, (∀ m ∈ L, m * l = l * m) → l = 1 := by
    intro l hl hm
    have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hm b b.2)
    rw [CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnab, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hKL : Subgroup.zpowers x ⊔ L ≤ C := sup_le (Subgroup.zpowers_le.2 hxC) hLC
  have h1 := CFSG.HardMathSupport.Dickson.I271.le_card_zpowers_sup hp hord hcomm hZ
  have h2 : Nat.card ↥(Subgroup.zpowers x ⊔ L) ≤ Nat.card ↥C := Subgroup.card_le_of_le hKL
  have hKC : Subgroup.zpowers x ⊔ L = C := Subgroup.eq_of_le_of_card_ge hKL (by omega)
  have hLn : ∀ g ∈ C, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
    rw [← hKC]
    exact CFSG.HardMathSupport.Dickson.I271.conj_mem_zpowers_sup hcomm
  have hLC' : L ≤ Subgroup.centralizer ({((⟨x, Subgroup.mem_top x⟩ : ↥(⊤ : Subgroup Q)) : Q)} :
      Set Q) ⊓ ⊤ := le_inf hLC le_top
  have hshape := CFSG.HardMathSupport.Dickson.I271.shapeRkAt_of_bound
    (Good := fun _ _ => True) (Rk := fun _ _ => True) hp (fun _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ => trivial) ⊤ ⟨x, Subgroup.mem_top x⟩ L hLC' hs hnab hpL hx1 hxp
    (by rw [inf_top_eq]; exact hbound) trivial trivial
  have hshape' := CFSG.HardMathSupport.Dickson.I271.ShapeRkAt.of_equiv hp
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) Subgroup.topEquiv hshape
  rcases hshape' with hc | ⟨J, hJ, -⟩
  · exact (false_of_pConstrainedShape_of_normal_simple hp hLC hLn hs hnab hc).elim
  · exact ⟨J, hJ⟩

theorem exists_glaPComponent_of_index2 {Q : Type} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    {x : Q} (hx1 : x ≠ 1) (hxp : x ^ p = 1) {L : Subgroup Q}
    (hLC : L ≤ Subgroup.centralizer ({x} : Set Q)) (hs : IsSimpleGroup ↥L)
    (hnab : ∃ a b : ↥L, a * b ≠ b * a) (hpL : p ∣ Nat.card ↥L)
    (hbound : Nat.card ↥(Subgroup.centralizer ({x} : Set Q)) ≤ 2 * (p * Nat.card ↥L)) :
    ∃ J : Subgroup Q, GLAPComponent p (Subgroup.centralizer ({x} : Set Q)) J := by
  haveI : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({x} : Set Q) with hC
  set K : Subgroup Q := Subgroup.zpowers x ⊔ L with hK
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hcomm : ∀ l ∈ L, l * x = x * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.1 (hLC hl)
  have hZL : Subgroup.center ↥L = ⊥ :=
    CFSG.HardMathSupport.Dickson.I271.center_eq_bot_of_simple_nonab hnab
  have hZ : ∀ l ∈ L, (∀ m ∈ L, m * l = l * m) → l = 1 := by
    intro l hl hm
    have hmem : (⟨l, hl⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext (hm b b.2)
    rw [hZL, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hKC : K ≤ C := sup_le (Subgroup.zpowers_le.2 hxC) hLC
  have hLK : L ≤ K := le_sup_right
  have hLn : ∀ g ∈ K, ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
    CFSG.HardMathSupport.Dickson.I271.conj_mem_zpowers_sup hcomm
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set Q) := by
    refine (Subgroup.zpowers_le.2 ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm l hl)
  have hKcard : Nat.card ↥K ≤ p * Nat.card ↥L := by
    have h := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hxN
    rw [sup_comm] at h
    have hpos : 0 < Nat.card ↥(L ⊓ Subgroup.zpowers x) := Nat.card_pos
    rw [Nat.card_zpowers, hord] at h
    nlinarith
  have h1 := CFSG.HardMathSupport.Dickson.I271.le_card_zpowers_sup hp hord hcomm hZ
  have hidx : (K.subgroupOf C).index ≤ 2 := by
    have hmul := (K.subgroupOf C).card_mul_index
    have hKs : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
    rw [hKs] at hmul
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    by_contra hgt
    push Not at hgt
    have : 3 * Nat.card ↥K ≤ Nat.card ↥C := by
      rw [← hmul]; nlinarith
    nlinarith
  have hKn : (K.subgroupOf C).Normal := by
    rcases (show (K.subgroupOf C).index = 1 ∨ (K.subgroupOf C).index = 2 by
      have := Subgroup.index_ne_zero_of_finite (H := K.subgroupOf C)
      omega) with h | h
    · rw [Subgroup.index_eq_one] at h
      rw [h]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h
  have hKsn : IsSubnormal K C := IsSubnormal.step hKC hKn (IsSubnormal.refl C)
  have hLq := KD264Gen.isQuasisimple_of_simple hnab
  have hcent : IsPGroup p ↥(K ⊓ Subgroup.centralizer (L : Set Q)) := by
    set H := K ⊓ Subgroup.centralizer (L : Set Q) with hH
    have hHN : H ≤ Subgroup.normalizer (L : Set Q) :=
      inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
    have hcard := CFSG.LocalAnalysis.GLTheoremA.card_sup_mul_card_inf_of_le_normalizer hHN
    have hinf : L ⊓ H = ⊥ := by
      rw [eq_bot_iff]
      intro l hl
      have hlL := (Subgroup.mem_inf.1 hl).1
      have hlc := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hl).2).2
      rw [Subgroup.mem_bot]
      exact hZ l hlL fun m hm => hlc m hm
    rw [hinf, Subgroup.card_bot, mul_one] at hcard
    have hsupK : L ⊔ H ≤ K := sup_le hLK inf_le_left
    have hle : Nat.card ↥L * Nat.card ↥H ≤ p * Nat.card ↥L := by
      rw [← hcard]
      exact (Subgroup.card_le_of_le hsupK).trans hKcard
    have hLpos : 0 < Nat.card ↥L := Nat.card_pos
    have hHp : Nat.card ↥H ≤ p := by nlinarith
    have hxH : x ∈ H := ⟨Subgroup.mem_sup_left (Subgroup.mem_zpowers x),
      Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm l hl)⟩
    have hdvd : p ∣ Nat.card ↥H := by
      rw [← hord, ← Subgroup.orderOf_mk x hxH]
      exact orderOf_dvd_natCard _
    have hHeq : Nat.card ↥H = p := le_antisymm hHp (Nat.le_of_dvd Nat.card_pos hdvd)
    exact IsPGroup.of_card (n := 1) (by rw [hHeq, pow_one])
  have hcoreK := CFSG.HardMathSupport.Dickson.I271.glaPPrimeCore_eq_bot_of_normal_quasisimple hp
    hLK hLn hLq hpL hcent
  have hcompK := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal_quasisimple hLK hLn hLq
    hcoreK
  exact ⟨L, CFSG.HardMathSupport.Solomon.LocalBalance.Lemma25Ns.glaPComponent_of_isSubnormal hp hKsn hcompK⟩

theorem kd264RowData_of_sq {T : Type} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (hsq : p ^ 2 ∣ Nat.card T) (hcube : ¬ p ^ 3 ∣ Nat.card T) (z₀ : T) (hz₀ : orderOf z₀ = p)
    {J₀ : Subgroup T} (hJ₀ : GLAPComponent p (Subgroup.centralizer ({z₀} : Set T)) J₀) :
    KD264RowData p T := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hno3 : ∀ S : Subgroup T, IsElemAbelian p S → Nat.card S < p ^ 3 := by
    intro S hS
    obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hS).exists_card_eq
    by_contra hge
    push Not at hge
    have hn3 : 3 ≤ n := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hn ▸ hge)
    exact hcube ((pow_dvd_pow p hn3).trans (hn ▸ Subgroup.card_subgroup_dvd_card S))
  have hzp : IsPGroup p (Subgroup.zpowers z₀) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hz₀, pow_one]
  obtain ⟨P₀, hzP₀⟩ := hzp.exists_le_sylow
  have hfac : (Nat.card T).factorization p = 2 := by
    have hT0 : Nat.card T ≠ 0 := Nat.card_pos.ne'
    have h2 : 2 ≤ (Nat.card T).factorization p := (hp.pow_dvd_iff_le_factorization hT0).1 hsq
    have h3 : ¬ 3 ≤ (Nat.card T).factorization p := fun h =>
      hcube ((hp.pow_dvd_iff_le_factorization hT0).2 h)
    omega
  have hP₀card : Nat.card (P₀ : Subgroup T) = p ^ 2 := by
    rw [Sylow.card_eq_multiplicity, hfac]
  have hcommP := IsPGroup.commutative_of_card_eq_prime_sq hP₀card
  refine kd264RowData_of_central hp hno3 z₀ hz₀ P₀ (fun g hg => ?_) hJ₀
  have h := hcommP ⟨g, hg⟩ ⟨z₀, hzP₀ (Subgroup.mem_zpowers z₀)⟩
  exact congrArg Subtype.val h

theorem prime_sq_dvd_mem {p N : ℕ} (hp : p.Prime) (hN : N ≠ 0) (h : p ^ 2 ∣ N) :
    p ∈ N.primeFactorsList.filter (fun q => q ^ 2 ∣ N) := by
  rw [List.mem_filter]
  exact ⟨(Nat.mem_primeFactorsList hN).2 ⟨hp, (dvd_pow_self p two_ne_zero).trans h⟩,
    decide_eq_true h⟩

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
