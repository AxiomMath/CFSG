module

public import CFSG.GroupTheory.SubnormalOddInversion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.SubnormalJoin
import CFSG.GroupTheory.BaerSuzuki.Helpers
import CFSG.LocalAnalysis.AGLEmbedding.CZeroLift
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe

open CFSG.Open Subgroup

open scoped commutatorElement

variable {V : Type} [Group V]

theorem perm_three_inv : ∀ x y : Equiv.Perm (Fin 3), x ^ 3 = 1 → y ^ 3 ≠ 1 →
    y ^ 2 = 1 ∧ y * x * y⁻¹ = x⁻¹ := by
  decide

theorem exists_inv_of_mulEquiv_perm_three {X : Subgroup V} (e : ↥X ≃* Equiv.Perm (Fin 3)) :
    ∃ s ∈ X, s ^ 2 = 1 ∧ s ^ 3 ≠ 1 ∧ ∀ x ∈ X, x ^ 3 = 1 → s * x * s⁻¹ = x⁻¹ := by
  set s : ↥X := e.symm (Equiv.swap 0 1) with hs
  have hes : e s = Equiv.swap 0 1 := by rw [hs, MulEquiv.apply_symm_apply]
  have hs3 : (e s) ^ 3 ≠ 1 := by rw [hes]; decide
  refine ⟨s, s.2, ?_, ?_, fun x hx hx3 => ?_⟩
  · have h := (perm_three_inv 1 (e s) (one_pow 3) hs3).1
    rw [← map_pow, ← map_one e] at h
    simpa using congrArg Subtype.val (e.injective h)
  · intro h
    apply hs3
    rw [← map_pow, show s ^ 3 = 1 from Subtype.ext (by simpa using h), map_one]
  · have hx3' : (e ⟨x, hx⟩) ^ 3 = 1 := by
      rw [← map_pow, show (⟨x, hx⟩ : ↥X) ^ 3 = 1 from Subtype.ext (by simpa using hx3), map_one]
    have h := (perm_three_inv (e ⟨x, hx⟩) (e s) hx3' hs3).2
    have h' : e (s * ⟨x, hx⟩ * s⁻¹) = e (⟨x, hx⟩⁻¹) := by
      rw [map_mul, map_mul, map_inv, map_inv]
      exact h
    simpa using congrArg Subtype.val (e.injective h')

theorem card_eq_six_of_mulEquiv_perm_three {X : Subgroup V} (e : ↥X ≃* Equiv.Perm (Fin 3)) :
    Nat.card X = 6 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

theorem eq_zpowers_sup_of_mulEquiv_perm_three [Finite V] {X : Subgroup V}
    (e : ↥X ≃* Equiv.Perm (Fin 3)) {z s : V} (hz : z ∈ X) (hzo : orderOf z = 3) (hs : s ∈ X)
    (hs2 : s ^ 2 = 1) (hs1 : s ≠ 1) : zpowers z ⊔ zpowers s = X := by
  have hle : zpowers z ⊔ zpowers s ≤ X := sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hs)
  have hso : orderOf s = 2 := orderOf_eq_prime hs2 hs1
  have h3 : 3 ∣ Nat.card ↥(zpowers z ⊔ zpowers s) := by
    rw [← hzo, ← Nat.card_zpowers]
    exact card_dvd_of_le le_sup_left
  have h2 : 2 ∣ Nat.card ↥(zpowers z ⊔ zpowers s) := by
    rw [← hso, ← Nat.card_zpowers]
    exact card_dvd_of_le le_sup_right
  have h6 : 6 ∣ Nat.card ↥(zpowers z ⊔ zpowers s) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 3 2) h3 h2
  have hX6 := card_eq_six_of_mulEquiv_perm_three e
  have hd : Nat.card ↥(zpowers z ⊔ zpowers s) ∣ 6 := hX6 ▸ card_dvd_of_le hle
  exact eq_of_le_of_card_ge hle (by rw [hX6, Nat.dvd_antisymm hd h6])

theorem mem_normalizer_zpowers_pow {g ρ : V} (h : g * ρ * g⁻¹ = ρ ∨ g * ρ * g⁻¹ = ρ⁻¹) (m : ℕ) :
    g ∈ normalizer ((zpowers (ρ ^ m) : Subgroup V) : Set V) := by
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  show zpowers ((MulAut.conj g) (ρ ^ m)) = zpowers (ρ ^ m)
  have hc : (MulAut.conj g) (ρ ^ m) = (g * ρ * g⁻¹) ^ m := by
    rw [MulAut.conj_apply, conj_pow]
  rcases h with h | h
  · rw [hc, h]
  · rw [hc, h, inv_pow, zpowers_inv]

theorem eq_of_isSubnormal_symThree [Finite V] (hV : CFSG.pCore 2 V = ⊥) {X W Z : Subgroup V}
    (hX : IsSubnormal X ⊤) (hW : IsSubnormal W ⊤) (eX : ↥X ≃* Equiv.Perm (Fin 3))
    (eW : ↥W ≃* Equiv.Perm (Fin 3)) (hZX : Z ≤ X) (hZW : Z ≤ W) (hZ : Nat.card Z = 3) :
    X = W := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z₀, hz₀⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hZ] : 3 ∣ Nat.card Z)
  set z : V := (z₀ : V) with hzdef
  have hzo : orderOf z = 3 := by rw [hzdef, orderOf_coe, hz₀]
  have hz3 : z ^ 3 = 1 := by rw [← hzo]; exact pow_orderOf_eq_one z
  have hzX : z ∈ X := hZX z₀.2
  have hzW : z ∈ W := hZW z₀.2
  obtain ⟨s, hsX, hs2, hs3, hsinv⟩ := exists_inv_of_mulEquiv_perm_three eX
  obtain ⟨s', hs'W, hs'2, hs'3, hs'inv⟩ := exists_inv_of_mulEquiv_perm_three eW
  have hs1 : s ≠ 1 := fun h => hs3 (by rw [h, one_pow])
  have hs'1 : s' ≠ 1 := fun h => hs'3 (by rw [h, one_pow])
  have hXg := eq_zpowers_sup_of_mulEquiv_perm_three eX hzX hzo hsX hs2 hs1
  have hWg := eq_zpowers_sup_of_mulEquiv_perm_three eW hzW hzo hs'W hs'2 hs'1
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hs2])
  have hs'i : s'⁻¹ = s' := inv_eq_of_mul_eq_one_right (by rw [← pow_two, hs'2])
  have hsz : s * z * s⁻¹ = z⁻¹ := hsinv z hzX hz3
  have hs'z : s' * z * s'⁻¹ = z⁻¹ := hs'inv z hzW hz3
  set ρ := s * s' with hρ
  have hρs : s * ρ * s⁻¹ = ρ⁻¹ := by
    rw [hρ, mul_inv_rev, hsi, hs'i]
    calc s * (s * s') * s = (s * s) * s' * s := by group
      _ = s' * s := by rw [← pow_two, hs2, one_mul]
  have hρs' : s' * ρ * s'⁻¹ = ρ⁻¹ := by
    rw [hρ, mul_inv_rev, hsi, hs'i]
    calc s' * (s * s') * s' = s' * s * (s' * s') := by group
      _ = s' * s := by rw [← pow_two, hs'2, mul_one]
  have hρz : z * ρ * z⁻¹ = ρ := by
    have hsz' : s * z⁻¹ * s⁻¹ = z := by
      rw [show s * z⁻¹ * s⁻¹ = (s * z * s⁻¹)⁻¹ by group, hsz, inv_inv]
    have hcomm : ρ * z = z * ρ := by
      calc ρ * z = s * (s' * z * s'⁻¹) * s' := by rw [hρ]; group
        _ = s * z⁻¹ * s' := by rw [hs'z]
        _ = (s * z⁻¹ * s⁻¹) * s * s' := by group
        _ = z * ρ := by rw [hsz', hρ, mul_assoc]
    rw [← hcomm]
    group
  set T := X ⊔ W with hT
  have hTsn : IsSubnormal T ⊤ := IsSubnormal.top_iff.2
    (CFSG.GroupTheory.isSubnormal_sup (IsSubnormal.top_iff.1 hX) (IsSubnormal.top_iff.1 hW))
  have hO : CFSG.pCore 2 ↥T = ⊥ := CFSG.AGLEmbedding.CZeroLift.pCore_eq_bot_of_isSubnormal hTsn hV
  have hρT : ρ ∈ T := T.mul_mem (le_sup_left (a := X) hsX) (le_sup_right (a := X) hs'W)
  have hodd : Odd (orderOf ρ) := by
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos ρ).ne'
    set U := zpowers (ρ ^ m) with hU
    have hN : T ≤ normalizer (U : Set V) := by
      have hz : z ∈ normalizer (U : Set V) := mem_normalizer_zpowers_pow (Or.inl hρz) m
      have hs : s ∈ normalizer (U : Set V) := mem_normalizer_zpowers_pow (Or.inr hρs) m
      have hs' : s' ∈ normalizer (U : Set V) := mem_normalizer_zpowers_pow (Or.inr hρs') m
      rw [hT, ← hXg, ← hWg]
      exact sup_le (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hs))
        (sup_le (zpowers_le.mpr hz) (zpowers_le.mpr hs'))
    have hUT : U ≤ T := zpowers_le.mpr (T.pow_mem hρT m)
    have hUp : IsPGroup 2 U := by
      have hd : orderOf (ρ ^ m) ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, mul_comm, ← hn, pow_orderOf_eq_one])
      obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
      exact IsPGroup.of_card (by rw [hU, Nat.card_zpowers, hb])
    have hle : U.subgroupOf T ≤ CFSG.pCore 2 ↥T :=
      CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup
        ((normal_subgroupOf_iff_le_normalizer hUT).2 hN) hUp.comap_subtype
    rw [hO] at hle
    have h1 : (⟨ρ ^ m, hUT (mem_zpowers _)⟩ : ↥T) ∈ (⊥ : Subgroup ↥T) :=
      hle (mem_subgroupOf.mpr (mem_zpowers _))
    have h2 : ρ ^ m = 1 := by simpa using congrArg Subtype.val (mem_bot.mp h1)
    exact hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
  have hXT : IsSubnormal X T := by
    have h := IsSubnormal.inf_of_le hX (le_top : T ≤ ⊤)
    rwa [inf_eq_left.mpr (le_sup_left : X ≤ T)] at h
  have hρX : ρ ∈ X := mem_of_isSubnormal_of_inv hXT hsX hρT hodd hρs
  have hs'X : s' ∈ X := by
    have h : s' = s⁻¹ * ρ := by rw [hρ, inv_mul_cancel_left]
    rw [h]
    exact X.mul_mem (X.inv_mem hsX) hρX
  have hWX : W ≤ X := hWg ▸ sup_le (zpowers_le.mpr hzX) (zpowers_le.mpr hs'X)
  exact (eq_of_le_of_card_ge hWX (by rw [card_eq_six_of_mulEquiv_perm_three eX,
    card_eq_six_of_mulEquiv_perm_three eW])).symm

theorem mem_of_isSubnormal_of_mul {X T : Subgroup V} (h : IsSubnormal X T) {p k : ℕ} {x y c : V}
    (hxT : x ∈ T) (hx : x ^ p ^ k = 1) (hy : y ∈ X) (hc : Nat.Coprime p (orderOf c))
    (hxyc : x = y * c) : x ∈ X := by
  induction h with
  | refl => exact hxT
  | @step X Y T hXY hn _ ih =>
    have hxY : x ∈ Y := ih hxT (hXY hy)
    have hcY : c ∈ Y := by
      have he : c = y⁻¹ * x := by rw [hxyc]; group
      rw [he]
      exact Y.mul_mem (Y.inv_mem (hXY hy)) hxY
    set q := QuotientGroup.mk' (X.subgroupOf Y) with hq
    have hqe : q ⟨x, hxY⟩ = q ⟨c, hcY⟩ := by
      have he : (⟨x, hxY⟩ : ↥Y) = ⟨y, hXY hy⟩ * ⟨c, hcY⟩ := Subtype.ext hxyc
      have hy1 : q ⟨y, hXY hy⟩ = 1 :=
        (QuotientGroup.eq_one_iff (⟨y, hXY hy⟩ : ↥Y)).mpr (mem_subgroupOf.mpr hy)
      rw [he, map_mul, hy1, one_mul]
    have h1 : orderOf (q ⟨x, hxY⟩) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, show (⟨x, hxY⟩ : ↥Y) ^ p ^ k = 1 from Subtype.ext (by simpa using hx),
        map_one])
    have h2 : orderOf (q ⟨x, hxY⟩) ∣ orderOf c := by
      rw [hqe, ← Subgroup.orderOf_mk c hcY]
      exact orderOf_map_dvd _ _
    have h3 : orderOf (q ⟨x, hxY⟩) = 1 :=
      ((Nat.Coprime.pow_left k hc).coprime_dvd_left h1).eq_one_of_dvd h2
    have h4 : q ⟨x, hxY⟩ = 1 := orderOf_eq_one_iff.mp h3
    exact mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (⟨x, hxY⟩ : ↥Y)).mp h4)

theorem commutator_zpowers_le_of_forall {J O : Subgroup V} {b : V}
    (hbJ : b ∈ normalizer (J : Set V)) (hbO : b ∈ normalizer (O : Set V))
    (h : ∀ x ∈ J, b * x * b⁻¹ * x⁻¹ ∈ O) : ⁅J, zpowers b⁆ ≤ O := by
  have hpow : ∀ n : ℤ, ∀ x ∈ J, b ^ n * x * b ^ (-n) * x⁻¹ ∈ O := by
    intro n
    induction n using Int.induction_on with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have h1 := ih x hx
      have h2 := (mem_normalizer_iff.mp hbO (b ^ (n : ℤ) * x * b ^ (-(n : ℤ)) * x⁻¹)).mp h1
      have he : b ^ ((n : ℤ) + 1) * x * b ^ (-((n : ℤ) + 1)) * x⁻¹ =
          (b * (b ^ (n : ℤ) * x * b ^ (-(n : ℤ)) * x⁻¹) * b⁻¹) * (b * x * b⁻¹ * x⁻¹) := by
        group
      rw [he]
      exact O.mul_mem h2 (h x hx)
    | pred n ih =>
      intro x hx
      have h1 := ih x hx
      have hbO' : b⁻¹ ∈ normalizer (O : Set V) := inv_mem hbO
      have hbJ' : b⁻¹ ∈ normalizer (J : Set V) := inv_mem hbJ
      have h2 := (mem_normalizer_iff.mp hbO' (b ^ (-(n : ℤ)) * x * b ^ (-(-(n : ℤ))) * x⁻¹)).mp
        h1
      have hx' : b⁻¹ * x * b⁻¹⁻¹ ∈ J := (mem_normalizer_iff.mp hbJ' x).mp hx
      have h3 := O.inv_mem (h _ hx')
      have he : b ^ (-(n : ℤ) - 1) * x * b ^ (-(-(n : ℤ) - 1)) * x⁻¹ =
          (b⁻¹ * (b ^ (-(n : ℤ)) * x * b ^ (-(-(n : ℤ))) * x⁻¹) * b⁻¹⁻¹) *
            (b * (b⁻¹ * x * b⁻¹⁻¹) * b⁻¹ * (b⁻¹ * x * b⁻¹⁻¹)⁻¹)⁻¹ := by group
      rw [he]
      exact O.mul_mem h2 h3
  rw [commutator_le]
  intro x hx g hg
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hg
  have h1 := O.inv_mem (hpow n x hx)
  have he : ⁅x, b ^ n⁆ = (b ^ n * x * b ^ (-n) * x⁻¹)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [he]
  exact h1

theorem perm_three_comm : ∀ w : Equiv.Perm (Fin 3), w ^ 3 ≠ 1 →
    ∃ r : Equiv.Perm (Fin 3), r * w * r⁻¹ * w⁻¹ ≠ 1 ∧ (r * w * r⁻¹ * w⁻¹) ^ 3 = 1 := by
  decide +kernel

theorem orderOf_perm_three_eq_three {σ : Equiv.Perm (Fin 3)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    orderOf σ = 3 :=
  orderOf_eq_prime h3 h1

theorem mem_pCore_of_symThree [Finite V] {I Y : Subgroup V}
    (e : ↥I ⧸ CFSG.pCore 2 ↥I ≃* Equiv.Perm (Fin 3))
    (hY : I ≤ normalizer (Y : Set V))
    (h3 : ∀ y ∈ I, y ∈ Y → ∀ k : ℕ, y ^ 3 ^ k = 1 → y = 1) :
    ∀ w : ↥I, (w : V) ∈ Y → w ∈ CFSG.pCore 2 ↥I := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥I) with hπ
  have key : ∀ w : ↥I, (w : V) ∈ Y → (e (π w)) ^ 3 = 1 → e (π w) = 1 := by
    intro w hwY hw3
    by_contra hne
    have ho : orderOf (e (π w)) = 3 := orderOf_perm_three_eq_three hw3 hne
    obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos w).ne' 3
      (by norm_num)
    have hwm : ((w : V) ^ m) ^ 3 ^ a = 1 := by
      rw [← pow_mul, mul_comm, ← hn, ← Subgroup.orderOf_coe, pow_orderOf_eq_one]
    have hwmY : (w : V) ^ m ∈ Y := Y.pow_mem hwY m
    have h1 : (w : V) ^ m = 1 := h3 _ (I.pow_mem w.2 m) hwmY a hwm
    have h2 : (e (π w)) ^ m = 1 := by
      rw [← map_pow, ← map_pow, show w ^ m = 1 from Subtype.ext (by simpa using h1), map_one,
        map_one]
    exact hm (ho ▸ orderOf_dvd_of_pow_eq_one h2)
  intro w hwY
  rw [← QuotientGroup.eq_one_iff]
  apply e.injective
  rw [map_one]
  by_cases hw3 : (e (π w)) ^ 3 = 1
  · exact key w hwY hw3
  · exfalso
    obtain ⟨r, hr1, hr3⟩ := perm_three_comm _ hw3
    obtain ⟨r', hr'₀⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I) (e.symm r)
    have hr' : π r' = e.symm r := hr'₀
    set w' : ↥I := r' * w * r'⁻¹ * w⁻¹ with hw'
    have hw'Y : (w' : V) ∈ Y := by
      have hc : (r' : V) * w * (r' : V)⁻¹ ∈ Y := (mem_normalizer_iff.mp (hY r'.2) w).mp hwY
      simpa [hw'] using Y.mul_mem hc (Y.inv_mem hwY)
    have hew : e (π w') = r * e (π w) * r⁻¹ * (e (π w))⁻¹ := by
      rw [hw', map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
        map_inv, hr', MulEquiv.apply_symm_apply]
    exact hr1 (hew ▸ key w' hw'Y (hew ▸ hr3))

theorem eq_bot_of_perfect_of_le {N X : Subgroup V} [Group.IsSolvable ↥N] (hXN : X ≤ N)
    (hX : ⁅X, X⁆ = X) : X = ⊥ := by
  by_contra hne
  set X' := X.subgroupOf N with hX'
  have hmap : X'.map N.subtype = X := map_subgroupOf_eq_of_le hXN
  have hne' : X' ≠ ⊥ := fun h => hne (by rw [← hmap, h, Subgroup.map_bot])
  have hlt := Group.IsSolvable.commutator_lt_of_ne_bot hne'
  have heq : ⁅X', X'⁆ = X' := by
    apply map_injective N.subtype_injective
    rw [map_commutator, hmap, hX]
  exact (ne_of_lt hlt) heq

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe
