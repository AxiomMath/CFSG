module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeFixedCommutator
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.GroupTheory.SteinbergBS

open Subgroup CFSG.LocalAnalysis.ComponentInitial

namespace PrimeQuotientObstruction

section Irreducible

variable {Γ : Type*} [Group Γ] {H Pb : Subgroup Γ}

theorem le_normalizer_of_conj_mem {K : Subgroup Γ} (h : ∀ x ∈ Pb, ∀ k ∈ K, x * k * x⁻¹ ∈ K) :
    Pb ≤ normalizer (K : Set Γ) := by
  intro x hx
  rw [mem_normalizer_iff]
  intro k
  refine ⟨h x hx k, fun hk => ?_⟩
  have h1 := h x⁻¹ (Pb.inv_mem hx) _ hk
  rwa [show x⁻¹ * (x * k * x⁻¹) * x⁻¹⁻¹ = k by group] at h1

theorem ne_bot_of_not_le_centralizer (hnt : ¬ Pb ≤ centralizer (H : Set Γ)) : H ≠ ⊥ := by
  rintro rfl
  exact hnt fun x _ => mem_centralizer_iff.2 fun h hh => by
    rw [SetLike.mem_coe, mem_bot] at hh
    rw [hh, one_mul, mul_one]

theorem inf_centralizer_eq_bot
    (hirr : ∀ K : Subgroup Γ, K ≤ H → Pb ≤ normalizer (K : Set Γ) → K = ⊥ ∨ K = H)
    (hnt : ¬ Pb ≤ centralizer (H : Set Γ)) : H ⊓ centralizer (Pb : Set Γ) = ⊥ := by
  have hn : Pb ≤ normalizer ((H ⊓ centralizer (Pb : Set Γ) : Subgroup Γ) : Set Γ) :=
    le_normalizer_of_conj_mem fun x hx k hk => by
      have hkx : x * k = k * x := mem_centralizer_iff.1 hk.2 x hx
      rw [hkx, mul_inv_cancel_right]
      exact hk
  rcases hirr _ inf_le_left hn with h | h
  · exact h
  · refine absurd (le_centralizer_iff.1 ?_) hnt
    rw [← h]
    exact inf_le_right

theorem card_modEq_one [Finite Γ] {p : ℕ} [Fact p.Prime] [H.Normal] (hPb : IsPGroup p Pb)
    (hC : H ⊓ centralizer (Pb : Set Γ) = ⊥) : Nat.card H ≡ 1 [MOD p] := by
  let _ : MulAction Pb H := MulAction.compHom H ((MulAut.conjNormal (H := H)).comp Pb.subtype)
  have hfix : MulAction.fixedPoints Pb H = {1} := by
    ext k
    rw [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hk
      have hkC : (k : Γ) ∈ H ⊓ centralizer (Pb : Set Γ) := by
        refine ⟨k.2, mem_centralizer_iff.2 fun x hx => ?_⟩
        have h1 : x * k * x⁻¹ = k := congrArg Subtype.val (hk ⟨x, hx⟩)
        calc x * k = x * k * x⁻¹ * x := by group
          _ = k * x := by rw [h1]
      rw [hC, mem_bot] at hkC
      exact Subtype.ext hkC
    · rintro rfl x
      exact map_one (MulAut.conjNormal (H := H) (x : Γ))
  have hmod := hPb.card_modEq_card_fixedPoints H
  rwa [hfix, Nat.card_unique (α := ↥({1} : Set H))] at hmod

end Irreducible

section Action

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] {H Pb : Subgroup Γ}

theorem false_of_pointwise_fixed [H.Normal]
    (hirr : ∀ K : Subgroup Γ, K ≤ H → Pb ≤ normalizer (K : Set Γ) → K = ⊥ ∨ K = H)
    (hnt : ¬ Pb ≤ centralizer (H : Set Γ)) {M : Set X} (hMH : ∀ h ∈ H, ∀ m ∈ M, h • m ∈ M)
    (hMP : ∀ x ∈ Pb, ∀ m ∈ M, x • m = m) (hMne : ∃ m ∈ M, ∃ h ∈ H, h • m ≠ m) : False := by
  let K : Subgroup Γ :=
    { carrier := {h | h ∈ H ∧ ∀ m ∈ M, h • m = m}
      mul_mem' := fun {a b} ha hb =>
        ⟨H.mul_mem ha.1 hb.1, fun m hm => by rw [mul_smul, hb.2 m hm, ha.2 m hm]⟩
      one_mem' := ⟨H.one_mem, fun m _ => one_smul Γ m⟩
      inv_mem' := fun {a} ha =>
        ⟨H.inv_mem ha.1, fun m hm => by rw [inv_smul_eq_iff, ha.2 m hm]⟩ }
  have hKn : Pb ≤ normalizer (K : Set Γ) := le_normalizer_of_conj_mem fun x hx k hk =>
    ⟨Normal.conj_mem inferInstance k hk.1 x, fun m hm => by
      rw [mul_smul, mul_smul, hMP x⁻¹ (Pb.inv_mem hx) m hm, hk.2 m hm, hMP x hx m hm]⟩
  rcases hirr K (fun h hh => hh.1) hKn with hK | hK
  · apply hnt
    intro x hx
    rw [mem_centralizer_iff]
    intro h hh
    have hc : h * x * h⁻¹ * x⁻¹ ∈ K := by
      refine ⟨?_, fun m hm => ?_⟩
      · have h1 : x * h⁻¹ * x⁻¹ ∈ H := Normal.conj_mem inferInstance _ (H.inv_mem hh) x
        have h2 := H.mul_mem hh h1
        rwa [show h * (x * h⁻¹ * x⁻¹) = h * x * h⁻¹ * x⁻¹ by group] at h2
      · rw [mul_smul, mul_smul, mul_smul, hMP x⁻¹ (Pb.inv_mem hx) m hm,
          hMP x hx _ (hMH h⁻¹ (H.inv_mem hh) m hm), smul_inv_smul]
    rw [hK, mem_bot] at hc
    calc h * x = h * x * h⁻¹ * x⁻¹ * (x * h) := by group
      _ = x * h := by rw [hc, one_mul]
  · obtain ⟨m, hm, h, hh, hne⟩ := hMne
    rw [← hK] at hh
    exact hne (hh.2 m hm)

theorem false_of_fixed_conj [H.Normal]
    (hirr : ∀ K : Subgroup Γ, K ≤ H → Pb ≤ normalizer (K : Set Γ) → K = ⊥ ∨ K = H)
    (hnt : ¬ Pb ≤ centralizer (H : Set Γ)) {v : X} (hvH : ∃ h ∈ H, h • v ≠ v)
    (hvP : ∀ x ∈ Pb, x • v = v) {h : Γ} (hh : h ∈ H) (h1 : h ≠ 1)
    (hvP' : ∀ x ∈ Pb, (h * x * h⁻¹) • v = v) : False := by
  have hKn : Pb ≤ normalizer ((H ⊓ MulAction.stabilizer Γ v : Subgroup Γ) : Set Γ) :=
    le_normalizer_of_conj_mem fun x hx k hk => ⟨Normal.conj_mem inferInstance k hk.1 x,
      MulAction.mem_stabilizer_iff.2 (by
        rw [mul_smul, mul_smul, hvP x⁻¹ (Pb.inv_mem hx), MulAction.mem_stabilizer_iff.1 hk.2,
          hvP x hx])⟩
  rcases hirr _ inf_le_left hKn with hK | hK
  · have hc : h ∈ H ⊓ centralizer (Pb : Set Γ) := by
      refine ⟨hh, mem_centralizer_iff.2 fun x hx => ?_⟩
      have hmem : h * x * h⁻¹ * x⁻¹ ∈ H ⊓ MulAction.stabilizer Γ v := by
        refine ⟨?_, ?_⟩
        · have h2 : x * h⁻¹ * x⁻¹ ∈ H := Normal.conj_mem inferInstance _ (H.inv_mem hh) x
          have h3 := H.mul_mem hh h2
          rwa [show h * (x * h⁻¹ * x⁻¹) = h * x * h⁻¹ * x⁻¹ by group] at h3
        · exact MulAction.mem_stabilizer_iff.2 (by
            rw [mul_smul, hvP x⁻¹ (Pb.inv_mem hx), hvP' x hx])
      rw [hK, mem_bot] at hmem
      calc x * h = (h * x * h⁻¹ * x⁻¹)⁻¹ * (h * x) := by group
        _ = h * x := by rw [hmem, inv_one, one_mul]
    rw [inf_centralizer_eq_bot hirr hnt, mem_bot] at hc
    exact h1 hc
  · obtain ⟨k, hk, hne⟩ := hvH
    rw [← hK] at hk
    exact hne (MulAction.mem_stabilizer_iff.1 hk.2)

end Action

theorem card_subtype_ne_add_one {M : Type*} [Finite M] (a : M) :
    Nat.card {x : M // x ≠ a} + 1 = Nat.card M := by
  classical
  rw [← Finite.card_option, Nat.card_congr (Equiv.optionSubtypeNe a)]

theorem false_of_card_eq_prime_or_sq {Γ X : Type*} [Group Γ] [Finite Γ] [AddCommGroup X]
    [DistribMulAction Γ X] {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hp2 : p ≠ 2)
    {H Pb : Subgroup Γ} [H.Normal] [IsElementaryAbelian q H] (hPb : Nat.card Pb = p)
    (hirr : ∀ K : Subgroup Γ, K ≤ H → Pb ≤ normalizer (K : Set Γ) → K = ⊥ ∨ K = H)
    (hnt : ¬ Pb ≤ centralizer (H : Set Γ)) (V : AddSubgroup X) [Finite V]
    (hVinv : ∀ x : Γ, ∀ v ∈ V, x • v ∈ V) (hCV : ∀ v ∈ V, (∀ h ∈ H, h • v = v) → v = 0)
    (hV : Nat.card V = p ∨ Nat.card V = p ^ 2) : False := by
  have hp1 := hp.out.one_lt
  have hPbp : IsPGroup p Pb := IsPGroup.of_card (n := 1) (by rw [hPb, pow_one])
  have hmoved : ∀ v ∈ V, v ≠ 0 → ∃ h ∈ H, h • v ≠ v := by
    intro v hv hv0
    by_contra hcon
    push Not at hcon
    exact hv0 (hCV v hv hcon)
  have hnz : ∀ K : AddSubgroup X, 1 < Nat.card K → ∃ v ∈ K, v ≠ 0 := by
    intro K hK
    have : Finite K := Nat.finite_of_card_ne_zero (by omega)
    have : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 hK
    obtain ⟨v, hv⟩ := exists_ne (0 : K)
    exact ⟨v, v.2, fun h => hv (Subtype.ext h)⟩
  have hVne : ∃ v ∈ V, v ≠ 0 := hnz V (by
    rcases hV with h | h <;> rw [h]
    · exact hp1
    · exact Nat.one_lt_pow two_ne_zero hp1)
  let L : AddSubgroup X :=
    { carrier := {v | v ∈ V ∧ ∀ x ∈ Pb, x • v = v}
      add_mem' := fun {a b} ha hb =>
        ⟨V.add_mem ha.1 hb.1, fun x hx => by rw [smul_add, ha.2 x hx, hb.2 x hx]⟩
      zero_mem' := ⟨V.zero_mem, fun x _ => smul_zero x⟩
      neg_mem' := fun {a} ha => ⟨V.neg_mem ha.1, fun x hx => by rw [smul_neg, ha.2 x hx]⟩ }
  have hLV : L ≤ V := fun v hv => hv.1
  have hLneV : ¬ V ≤ L := by
    intro hVL
    obtain ⟨v, hv, hv0⟩ := hVne
    exact false_of_pointwise_fixed hirr hnt (M := (V : Set X)) (fun h _ m hm => hVinv h m hm)
      (fun x hx m hm => (hVL hm).2 x hx) ⟨v, hv, hmoved v hv hv0⟩
  let _ : MulAction Pb V :=
    { smul := fun x v => ⟨(x : Γ) • (v : X), hVinv x v v.2⟩
      one_smul := fun v => Subtype.ext (one_smul Γ (v : X))
      mul_smul := fun x y v => Subtype.ext (mul_smul (x : Γ) (y : Γ) (v : X)) }
  have hfixL : Nat.card (MulAction.fixedPoints Pb V) = Nat.card L := Nat.card_congr
    { toFun := fun w => ⟨w.1.1, w.1.2, fun x hx =>
        congrArg Subtype.val (MulAction.mem_fixedPoints.1 w.2 ⟨x, hx⟩)⟩
      invFun := fun l => ⟨⟨l.1, l.2.1⟩, MulAction.mem_fixedPoints.2 fun x =>
        Subtype.ext (l.2.2 x x.2)⟩
      left_inv := fun w => rfl
      right_inv := fun l => rfl }
  have hmod := hPbp.card_modEq_card_fixedPoints V
  rw [hfixL] at hmod
  have hLdvd : Nat.card L ∣ Nat.card V := AddSubgroup.card_dvd_of_le hLV
  have hLne : Nat.card L ≠ Nat.card V := fun h =>
    hLneV (AddSubgroup.eq_of_le_of_card_ge hLV h.symm.le).ge
  have hpV : p ∣ Nat.card V := by
    rcases hV with h | h
    · exact h ▸ dvd_refl p
    · exact h ▸ dvd_pow_self p two_ne_zero
  have hpL : p ∣ Nat.card L :=
    Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 hpV))
  obtain ⟨hV2, hL⟩ : Nat.card V = p ^ 2 ∧ Nat.card L = p := by
    rcases hV with h | h
    · rw [h] at hLdvd hLne
      exact absurd (Nat.dvd_antisymm hLdvd hpL) hLne
    · refine ⟨h, ?_⟩
      rw [h] at hLdvd hLne
      obtain ⟨j, hj, hjL⟩ := (Nat.dvd_prime_pow hp.out).1 hLdvd
      rw [hjL] at hpL hLne ⊢
      interval_cases j
      · rw [pow_zero, Nat.dvd_one] at hpL
        omega
      · exact pow_one p
      · exact absurd rfl hLne
  have : Finite L := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨v₀, hv₀, hv₀0⟩ := hnz L (by rw [hL]; exact hp1)
  let HL : Subgroup Γ :=
    { carrier := {h | h ∈ H ∧ ∀ v, v ∈ L ↔ h • v ∈ L}
      mul_mem' := fun {a b} ha hb =>
        ⟨H.mul_mem ha.1 hb.1, fun v => by rw [mul_smul, ← ha.2, ← hb.2]⟩
      one_mem' := ⟨H.one_mem, fun v => by rw [one_smul]⟩
      inv_mem' := fun {a} ha =>
        ⟨H.inv_mem ha.1, fun v => by rw [ha.2 (a⁻¹ • v), smul_inv_smul]⟩ }
  have hLP : ∀ x ∈ Pb, ∀ v, v ∈ L ↔ x • v ∈ L := by
    intro x hx v
    refine ⟨fun hv => by rw [hv.2 x hx]; exact hv, fun hv => ?_⟩
    have h1 : x⁻¹ • x • v = x • v := hv.2 x⁻¹ (Pb.inv_mem hx)
    rw [inv_smul_smul] at h1
    rw [h1]
    exact hv
  have hHLn : Pb ≤ normalizer (HL : Set Γ) := le_normalizer_of_conj_mem fun x hx k hk =>
    ⟨Normal.conj_mem inferInstance k hk.1 x, fun v => by
      rw [mul_smul, mul_smul, ← hLP x hx, ← hk.2, ← hLP x⁻¹ (Pb.inv_mem hx)]⟩
  have hmul : ∀ u ∈ L, u ≠ 0 → ∀ w ∈ L, ∃ n : ℤ, w = n • u := by
    intro u hu hu0 w hw
    have h1 : (⟨w, hw⟩ : L) ∈ AddSubgroup.zmultiples (⟨u, hu⟩ : L) :=
      mem_zmultiples_of_prime_card hL fun h => hu0 (congrArg Subtype.val h)
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
    exact ⟨n, (congrArg Subtype.val hn).symm⟩
  have hgen : ∀ k ∈ H, ∀ v ∈ L, v ≠ 0 → k • v ∈ L → k ∈ HL := by
    intro k hk v hv hv0 hkv
    refine ⟨hk, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩
    · obtain ⟨n, rfl⟩ := hmul v hv hv0 w hw
      rw [smul_comm k n v]
      exact L.zsmul_mem hkv n
    · have hkv0 : k • v ≠ 0 := fun h => hv0 ((smul_eq_zero_iff_eq k).1 h)
      obtain ⟨n, hn⟩ := hmul (k • v) hkv hkv0 (k • w) hw
      rw [← smul_comm k n v] at hn
      rw [(smul_left_cancel_iff k).1 hn]
      exact L.zsmul_mem hv n
  rcases hirr HL (fun h hh => hh.1) hHLn with hHL | hHL
  ·
    have hstab : ∀ k ∈ H, ∀ v ∈ L, v ≠ 0 → k • v ∈ L → k = 1 := fun k hk v hv hv0 hkv => by
      have h1 := hgen k hk v hv hv0 hkv
      rwa [hHL, mem_bot] at h1
    let f : H × {v : L // v ≠ 0} → {w : V // w ≠ 0} := fun kv =>
      ⟨⟨(kv.1 : Γ) • ((kv.2 : L) : X), hVinv _ _ (hLV (kv.2 : L).2)⟩, fun h0 =>
        kv.2.2 (Subtype.ext ((smul_eq_zero_iff_eq (kv.1 : Γ)).1 (congrArg Subtype.val h0)))⟩
    have hf : Function.Injective f := by
      rintro ⟨k, v⟩ ⟨k', v'⟩ heq
      have h1 : (k : Γ) • ((v : L) : X) = (k' : Γ) • ((v' : L) : X) :=
        congrArg (fun w : {w : V // w ≠ 0} => ((w : V) : X)) heq
      have h2 : ((k' : Γ)⁻¹ * k) • ((v : L) : X) = ((v' : L) : X) := by
        rw [mul_smul, h1, inv_smul_smul]
      have h3 := hstab _ (H.mul_mem (H.inv_mem k'.2) k.2) _ (v : L).2
        (fun h => v.2 (Subtype.ext h)) (by rw [h2]; exact (v' : L).2)
      have hkk : (k : Γ) = k' := (inv_mul_eq_one.1 h3).symm
      rw [hkk] at h1
      have hvv : ((v : L) : X) = ((v' : L) : X) := (smul_left_cancel_iff _).1 h1
      exact Prod.ext (Subtype.ext hkk) (Subtype.ext (Subtype.ext hvv))
    set a := Nat.card {v : L // v ≠ 0} with ha
    set b := Nat.card {w : V // w ≠ 0} with hb'
    have hcardL : a + 1 = p := by rw [← hL]; exact card_subtype_ne_add_one 0
    have hcardV : b + 1 = p ^ 2 := by rw [← hV2]; exact card_subtype_ne_add_one 0
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod] at hle
    have hb : b = (a + 2) * a := by
      have h1 : b + 1 = (a + 1) ^ 2 := by rw [hcardV, hcardL]
      nlinarith [h1]
    have hHle : Nat.card H ≤ p + 1 := by
      have ha0 : 0 < a := by omega
      have h1 : Nat.card H * a ≤ (a + 2) * a := hle.trans_eq hb
      have h2 := Nat.le_of_mul_le_mul_right h1 ha0
      omega
    have hHmod := card_modEq_one hPbp (inf_centralizer_eq_bot hirr hnt)
    have hHne := ne_bot_of_not_le_centralizer hnt
    have hH1 : 1 < Nat.card H := by
      by_contra h
      push Not at h
      exact hHne (eq_bot_of_card_eq H (le_antisymm h Nat.card_pos))
    have hHp1 : Nat.card H = p + 1 := by
      have h1 : p ∣ Nat.card H - 1 := (Nat.modEq_iff_dvd' Nat.card_pos).1 hHmod.symm
      have h2 : p ≤ Nat.card H - 1 := Nat.le_of_dvd (by omega) h1
      omega
    have hq2 : q = 2 := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (IsElementaryAbelian.isPGroup q H)
      have hodd : p % 2 = 1 := hp.out.eq_two_or_odd.resolve_left hp2
      have h2 : 2 ∣ q ^ n := by rw [← hn, hHp1]; omega
      exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq.out).1
        (Nat.prime_two.dvd_of_dvd_pow h2)).symm
    have hsurj : Function.Surjective f := (hf.bijective_of_nat_card_le (by
      rw [Nat.card_prod, hHp1, ← hb', hb, ← hcardL])).2
    obtain ⟨⟨h, hhH⟩, hh1⟩ := (ne_bot_iff_exists_ne_one).1 hHne
    have hh1' : h ≠ 1 := fun h' => hh1 (Subtype.ext h')
    have hh2 : h * h = 1 := by
      have h1 := elemPow_eq_one_of_isElementaryAbelian (p := q) (A := H) h hhH
      rwa [hq2, pow_two] at h1
    have hcomm : ∀ k : H, h * k = k * h := fun k =>
      congrArg Subtype.val (mul_comm' (⟨h, hhH⟩ : H) k)
    by_cases hw0 : v₀ + h • v₀ = 0
    · have h1 : h • v₀ = -v₀ := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hw0
      exact hh1' (hstab h hhH v₀ hv₀ hv₀0 (by rw [h1]; exact L.neg_mem hv₀))
    · have hwV : v₀ + h • v₀ ∈ V := V.add_mem (hLV hv₀) (hVinv h v₀ (hLV hv₀))
      obtain ⟨⟨k, v⟩, hkv⟩ := hsurj ⟨⟨v₀ + h • v₀, hwV⟩, fun h0 => hw0 (congrArg Subtype.val h0)⟩
      have h1 : (k : Γ) • ((v : L) : X) = v₀ + h • v₀ :=
        congrArg (fun w : {w : V // w ≠ 0} => ((w : V) : X)) hkv
      have hhw : h • (v₀ + h • v₀) = v₀ + h • v₀ := by
        rw [smul_add, smul_smul, hh2, one_smul, add_comm]
      have h2 : h • ((v : L) : X) = ((v : L) : X) := by
        rw [← h1, smul_smul, hcomm k, mul_smul] at hhw
        exact (smul_left_cancel_iff _).1 hhw
      exact hh1' (hstab h hhH _ (v : L).2 (fun h0 => v.2 (Subtype.ext h0))
        (by rw [h2]; exact (v : L).2))
  ·
    refine false_of_pointwise_fixed hirr hnt (M := (L : Set X)) (fun h hh m hm => ?_)
      (fun x hx m hm => hm.2 x hx) ⟨v₀, hv₀, hmoved v₀ hv₀.1 hv₀0⟩
    have hh' : h ∈ HL := by rw [hHL]; exact hh
    exact (hh'.2 m).1 hm


section Group

variable {G : Type*} [Group G]

theorem isPGroup_of_hasNormalPComplement [Finite G] {p : ℕ} [Fact p.Prime] {Q C : Subgroup G}
    [Q.Normal] (hQ : IsPGroup p Q) (hCQ : centralizer (Q : Set G) ≤ Q) (hQC : Q ≤ C)
    (hC : CFSG.HasNormalPComplement p C) : IsPGroup p C := by
  obtain ⟨N, hN, hcop, hquot⟩ := hC
  have hQN : ∀ x : G, x ∈ Q → x ^ Nat.card N = 1 → x = 1 := by
    intro x hx hxN
    obtain ⟨k, hk⟩ := hQ ⟨x, hx⟩
    have h1 : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      have h2 := congrArg Subtype.val hk
      simpa using h2)
    have h2 : orderOf x ∣ Nat.card N := orderOf_dvd_of_pow_eq_one hxN
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) h1 h2)
  have hpowN : ∀ n ∈ N, ((n : C) : G) ^ Nat.card N = 1 := by
    intro n hn
    have h1 : (⟨n, hn⟩ : N) ^ Nat.card N = 1 := pow_card_eq_one'
    have h2 := congrArg (fun y : N => ((y : C) : G)) h1
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    exact h2
  have hN1 : ∀ n ∈ N, ((n : C) : G) = 1 := by
    intro n hn
    have hnQ : ((n : C) : G) ∈ Q := by
      apply hCQ
      rw [mem_centralizer_iff]
      intro x hx
      have hc : n * ((⟨x, hQC hx⟩ : C) * n⁻¹ * (⟨x, hQC hx⟩ : C)⁻¹) ∈ N :=
        N.mul_mem hn (hN.conj_mem _ (N.inv_mem hn) _)
      have hcQ : (n : G) * (x * (n : G)⁻¹ * x⁻¹) ∈ Q := by
        have h1 : (n : G) * x * (n : G)⁻¹ ∈ Q := Normal.conj_mem inferInstance x hx n
        have h2 := Q.mul_mem h1 (Q.inv_mem hx)
        rwa [show (n : G) * x * (n : G)⁻¹ * x⁻¹ = (n : G) * (x * (n : G)⁻¹ * x⁻¹) by group]
          at h2
      have h3 : (n : G) * (x * (n : G)⁻¹ * x⁻¹) = 1 := hQN _ hcQ (by
        have h4 := hpowN _ hc
        simpa using h4)
      calc x * n = ((n : G) * (x * (n : G)⁻¹ * x⁻¹))⁻¹ * (n * x) := by group
        _ = n * x := by rw [h3, inv_one, one_mul]
    exact hQN _ hnQ (hpowN n hn)
  intro c
  obtain ⟨k, hk⟩ := hquot (c : C ⧸ N)
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : c ^ p ^ k ∈ N := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using hk
  simpa using hN1 _ h1

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
theorem isElementaryAbelian_of_le {H K : Subgroup G} [IsElementaryAbelian p K] (hHK : H ≤ K) :
    IsElementaryAbelian p H := CFSG.IsElementaryAbelian.of_le inferInstance hHK

omit hp in
theorem map_conj_eq_of_normal (V : Subgroup G) [V.Normal] (g : G) :
    V.map (MulAut.conj g).toMonoidHom = V := by
  refine le_antisymm ?_ fun x hx => ⟨g⁻¹ * x * g, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact Normal.conj_mem inferInstance y hy g
  · have h1 := Normal.conj_mem (inferInstance : V.Normal) x hx g⁻¹
    rwa [inv_inv] at h1
  · change g * (g⁻¹ * x * g) * g⁻¹ = x
    group

theorem exists_mem_inf_conj [Finite G] {P Q A V : Subgroup G} [Q.Normal] [V.Normal]
    [IsElementaryAbelian p A] [IsElementaryAbelian p V] (hQA : Q ⊔ A = P) (hVQ : V ≤ Q)
    (hVC : V ≤ centralizer (Q : Set G))
    (hAmax : ∀ B : Subgroup G, B ≤ P → IsElementaryAbelian p B → Nat.card B ≤ Nat.card A)
    (hPb : Nat.card (P.map (QuotientGroup.mk' Q)) = p) (g : G) (hV : p ^ 3 ≤ Nat.card V) :
    ∃ x ∈ V, x ≠ 1 ∧ x ∈ A ∧ g⁻¹ * x * g ∈ A := by
  have hA₀A : Q ⊓ A ≤ A := inf_le_right
  have hA₀Q : Q ⊓ A ≤ Q := inf_le_left
  have : IsElementaryAbelian p ↥(Q ⊓ A) := isElementaryAbelian_of_le hA₀A
  have hAcard : Nat.card A ≤ p * Nat.card ↥(Q ⊓ A) := by
    have h1 := relIndex_mul_card Q A
    have h2 : Q.relIndex A = Nat.card (A.map (QuotientGroup.mk' Q)) := by
      rw [← relIndex_ker, QuotientGroup.ker_mk']
    have h3 : Nat.card (A.map (QuotientGroup.mk' Q)) ≤ p := by
      rw [← hPb]
      exact card_le_of_le (map_mono (hQA ▸ le_sup_right))
    rw [← h1, h2]
    exact Nat.mul_le_mul_right _ h3
  have hA₀V : Q ⊓ A ≤ centralizer (V : Set G) := hA₀Q.trans (le_centralizer_iff.1 hVC)
  have hB : IsElementaryAbelian p ↥(V ⊔ Q ⊓ A) :=
    IsElementaryAbelian.sup_of_le_centralizer hA₀V
  have hBP : V ⊔ Q ⊓ A ≤ P :=
    sup_le (hVQ.trans (hQA ▸ le_sup_left)) (hA₀A.trans (hQA ▸ le_sup_right))
  have hBcard := hAmax _ hBP hB
  have hVn : V ≤ normalizer ((Q ⊓ A : Subgroup G) : Set G) :=
    (le_centralizer_iff.1 hA₀V).trans (centralizer_le_normalizer _)
  have hidx : (Q ⊓ A).relIndex V = (Q ⊓ A).relIndex (V ⊔ Q ⊓ A) :=
    Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient V (Q ⊓ A) hVn).toEquiv
  have hidx' : (Q ⊓ A).relIndex V ≤ p := by
    have h1 := relIndex_mul_card (Q ⊓ A) (V ⊔ Q ⊓ A)
    rw [inf_of_le_left (le_sup_right : Q ⊓ A ≤ V ⊔ Q ⊓ A), ← hidx] at h1
    have h2 : (Q ⊓ A).relIndex V * Nat.card ↥(Q ⊓ A) ≤ p * Nat.card ↥(Q ⊓ A) := by
      rw [h1]
      exact hBcard.trans hAcard
    exact Nat.le_of_mul_le_mul_right h2 Nat.card_pos
  have hidxc : ((Q ⊓ A).comap (MulAut.conj g⁻¹).toMonoidHom).relIndex V ≤ p := by
    rw [relIndex_comap, map_conj_eq_of_normal]
    exact hidx'
  have hint : ((Q ⊓ A) ⊓ (Q ⊓ A).comap (MulAut.conj g⁻¹).toMonoidHom).relIndex V ≤ p * p :=
    relIndex_inf_le.trans (Nat.mul_le_mul hidx' hidxc)
  have hcard := relIndex_mul_card ((Q ⊓ A) ⊓ (Q ⊓ A).comap (MulAut.conj g⁻¹).toMonoidHom) V
  have hbig : 1 < Nat.card
      ↥((Q ⊓ A) ⊓ (Q ⊓ A).comap (MulAut.conj g⁻¹).toMonoidHom ⊓ V) := by
    by_contra hle
    push Not at hle
    have h1 : Nat.card V ≤ p * p := by
      rw [← hcard]
      calc _ ≤ p * p * 1 := Nat.mul_le_mul hint hle
        _ = p * p := mul_one _
    have h2 : p * p * p ≤ p * p * 1 := by
      calc p * p * p = p ^ 3 := by ring
        _ ≤ Nat.card V := hV
        _ ≤ p * p := h1
        _ = p * p * 1 := (mul_one _).symm
    have h3 := Nat.le_of_mul_le_mul_left h2 (Nat.mul_pos hp.out.pos hp.out.pos)
    exact absurd h3 (by have := hp.out.one_lt; omega)
  have : Nontrivial ↥((Q ⊓ A) ⊓ (Q ⊓ A).comap (MulAut.conj g⁻¹).toMonoidHom ⊓ V) :=
    Finite.one_lt_card_iff_nontrivial.1 hbig
  obtain ⟨⟨x, ⟨⟨hxA₀, hxc⟩, hxV⟩⟩, hx1⟩ := exists_ne
    (1 : ↥((Q ⊓ A) ⊓ (Q ⊓ A).comap (MulAut.conj g⁻¹).toMonoidHom ⊓ V))
  refine ⟨x, hxV, fun h => hx1 (Subtype.ext h), hA₀A hxA₀, ?_⟩
  have h1 : (MulAut.conj g⁻¹).toMonoidHom x = g⁻¹ * x * g := by
    change g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g
    rw [inv_inv]
  exact hA₀A (h1 ▸ hxc)

@[expose] noncomputable def quotientConjHom (Q Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hQZ : Q ≤ centralizer (Z : Set G)) : G ⧸ Q →* MulAut Z :=
  QuotientGroup.lift Q MulAut.conjNormal fun x hx => (MonoidHom.mem_ker).2 <|
    MulEquiv.ext fun z => Subtype.ext (by
      rw [MulAut.conjNormal_apply, MulAut.one_apply, ← mem_centralizer_iff.1 (hQZ hx) z z.2,
        mul_inv_cancel_right])

@[expose, instance_reducible]
noncomputable def quotientConjAct (Q Z : Subgroup G) [Q.Normal] [Z.Normal]
    (hQZ : Q ≤ centralizer (Z : Set G)) : DistribMulAction (G ⧸ Q) (Additive Z) where
  smul x z := Additive.ofMul (quotientConjHom Q Z hQZ x z.toMul)
  one_smul z := by
    change Additive.ofMul (quotientConjHom Q Z hQZ 1 z.toMul) = z
    rw [map_one, MulAut.one_apply, ofMul_toMul]
  mul_smul x y z := by
    change Additive.ofMul (quotientConjHom Q Z hQZ (x * y) z.toMul) =
      Additive.ofMul (quotientConjHom Q Z hQZ x (quotientConjHom Q Z hQZ y z.toMul))
    rw [map_mul, MulAut.mul_apply]
  smul_zero x := by
    change Additive.ofMul (quotientConjHom Q Z hQZ x 1) = Additive.ofMul 1
    rw [map_one]
  smul_add x z w := by
    change Additive.ofMul (quotientConjHom Q Z hQZ x (z.toMul * w.toMul)) =
      Additive.ofMul (quotientConjHom Q Z hQZ x z.toMul * quotientConjHom Q Z hQZ x w.toMul)
    rw [map_mul]

end Group

end PrimeQuotientObstruction

open PrimeQuotientObstruction in
theorem maximal_elementary_sylow_prime_quotient_obstruction {G : Type*} [Group G] [Finite G]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime] (hp2 : p ≠ 2) (hqp : q ≠ p)
    (P : Sylow p G) (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q)
    (hCQ : centralizer (Q : Set G) ≤ Q) (H : Subgroup (G ⧸ Q)) [H.Normal]
    [IsElementaryAbelian q H] (hPb : Nat.card ((P : Subgroup G).map (QuotientGroup.mk' Q)) = p)
    (hnt : ¬ (P : Subgroup G).map (QuotientGroup.mk' Q) ≤ centralizer (H : Set (G ⧸ Q)))
    (hirr : ∀ K : Subgroup (G ⧸ Q), K ≤ H →
      (P : Subgroup G).map (QuotientGroup.mk' Q) ≤ normalizer (K : Set (G ⧸ Q)) →
        K = ⊥ ∨ K = H)
    (A : Subgroup G) [IsElementaryAbelian p A]
    (hAmax : ∀ B : Subgroup G, B ≤ P → IsElementaryAbelian p B → Nat.card B ≤ Nat.card A)
    (hQA : Q ⊔ A = P) :
    ¬ CFSG.HasNormalPComplement p
      ↥(centralizer (((center (P : Subgroup G)).map (P : Subgroup G).subtype : Subgroup G) :
        Set G)) := by
  intro hC
  have hQP : Q ≤ P := hQA ▸ le_sup_left
  have hZPQ : (center (P : Subgroup G)).map (P : Subgroup G).subtype ≤
      centralizer (Q : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_centralizer_iff.2 fun x hx =>
      congrArg Subtype.val (mem_center_iff.1 hz ⟨x, hQP hx⟩)
  have hCp := isPGroup_of_hasNormalPComplement hQ hCQ (le_centralizer_iff.1 hZPQ) hC
  set Z := centralizer (Q : Set G) with hZ
  have hQZ : Q ≤ centralizer (Z : Set G) := le_centralizer_iff.1 le_rfl
  have hZcomm : IsMulCommutative Z := le_centralizer_iff_isMulCommutative.1 (hCQ.trans hQZ)
  let _ : CommGroup Z := { (inferInstance : Group Z) with mul_comm := hZcomm.is_comm.comm }
  let _ := quotientConjAct Q Z hQZ
  have hsm : ∀ (y z : G) (hz : z ∈ Z), QuotientGroup.mk' Q y • Additive.ofMul (⟨z, hz⟩ : Z) =
      Additive.ofMul (⟨y * z * y⁻¹, Normal.conj_mem inferInstance z hz y⟩ : Z) :=
    fun _ _ _ => rfl
  have hZp : IsPGroup p Z := hQ.to_le hCQ
  have hHq : IsPGroup q H := IsElementaryAbelian.isPGroup q H
  have hcop : Nat.Coprime (Nat.card H) (Nat.card (Additive Z)) := by
    rw [show Nat.card (Additive Z) = Nat.card Z from Nat.card_congr Additive.toMul]
    exact IsPGroup.coprime_card_of_ne q p hqp H Z hHq hZp
  obtain ⟨hcompl, hinv⟩ := abelian_coprime_fixed_commutator_decomposition H hcop
  set W := coprimeCommutator H (Additive Z) with hW
  have hWinv : ∀ x : G ⧸ Q, ∀ w ∈ W, x • w ∈ W := fun x w hw => (hinv inferInstance x).1 w hw
  have hHne := ne_bot_of_not_le_centralizer hnt
  have hWne : W ≠ ⊥ := by
    intro hW0
    have htriv : ∀ h ∈ H, ∀ z : Additive Z, h • z = z := by
      intro h hh z
      have hmem : h • z - z ∈ W := AddSubgroup.subset_closure ⟨h, hh, z, rfl⟩
      rwa [hW0, AddSubgroup.mem_bot, sub_eq_zero] at hmem
    have hHC : H ≤ (centralizer (((center (P : Subgroup G)).map (P : Subgroup G).subtype :
        Subgroup G) : Set G)).map (QuotientGroup.mk' Q) := by
      intro h hh
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q h
      refine ⟨g, mem_centralizer_iff.2 fun z hz => ?_, rfl⟩
      have h1 := congrArg (fun w : Additive Z => ((w.toMul : Z) : G))
        (htriv _ hh (Additive.ofMul ⟨z, hZPQ hz⟩))
      change g * z * g⁻¹ = z at h1
      calc z * g = g * z * g⁻¹ * g := by rw [h1]
        _ = g * z := by group
    have hHp : IsPGroup p H := (hCp.map _).to_le hHC
    have h1 : Nat.card H = 1 :=
      (Nat.coprime_self _).1 (IsPGroup.coprime_card_of_ne p q hqp.symm H H hHp hHq)
    exact hHne (eq_bot_of_card_eq H h1)
  let V : AddSubgroup (Additive Z) :=
    { carrier := {w | w ∈ W ∧ p • w = 0}
      add_mem' := fun {a b} ha hb =>
        ⟨W.add_mem ha.1 hb.1, by rw [nsmul_add, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨W.zero_mem, nsmul_zero p⟩
      neg_mem' := fun {a} ha => ⟨W.neg_mem ha.1, by rw [smul_neg, ha.2, neg_zero]⟩ }
  have hVinv : ∀ x : G ⧸ Q, ∀ v ∈ V, x • v ∈ V := fun x v hv =>
    ⟨hWinv x v hv.1, by rw [← smul_comm x p v, hv.2, smul_zero]⟩
  have hCV : ∀ v ∈ V, (∀ h ∈ H, h • v = v) → v = 0 := by
    intro v hv hfix
    have h1 : v ∈ W ⊓ coprimeFixed H (Additive Z) := ⟨hv.1, mem_coprimeFixed.2 hfix⟩
    rwa [hcompl.inf_eq_bot, AddSubgroup.mem_bot] at h1
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hZp
  have hcardZ : Nat.card (Additive Z) = p ^ k := by
    rw [← hk]
    exact Nat.card_congr Additive.toMul
  have hVne : ∃ v ∈ V, v ≠ 0 := by
    have hWdvd : Nat.card W ∣ p ^ k := hcardZ ▸ AddSubgroup.card_addSubgroup_dvd_card W
    have hWcard : p ∣ Nat.card W := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hWdvd
      have hj0 : j ≠ 0 := by
        rintro rfl
        exact hWne (AddSubgroup.eq_bot_of_card_eq W (by rw [hj, pow_zero]))
      rw [hj]
      exact dvd_pow_self p hj0
    obtain ⟨w, hw⟩ := exists_prime_addOrderOf_dvd_card' p hWcard
    refine ⟨w, ⟨w.2, ?_⟩, fun h0 => ?_⟩
    · have h1 := addOrderOf_nsmul_eq_zero w
      rw [hw] at h1
      exact congrArg Subtype.val h1
    · have h1 : w = 0 := Subtype.ext h0
      rw [h1, addOrderOf_zero] at hw
      exact hp.out.one_lt.ne hw
  let V' : Subgroup G :=
    { carrier := {x | ∃ hx : x ∈ Z, Additive.ofMul (⟨x, hx⟩ : Z) ∈ V}
      mul_mem' := fun {a b} ha hb => ⟨Z.mul_mem ha.fst hb.fst, V.add_mem ha.snd hb.snd⟩
      one_mem' := ⟨Z.one_mem, V.zero_mem⟩
      inv_mem' := fun {a} ha => ⟨Z.inv_mem ha.fst, V.neg_mem ha.snd⟩ }
  have hV'Z : V' ≤ Z := fun x hx => hx.fst
  have hV'Q : V' ≤ Q := hV'Z.trans hCQ
  have hV'n : V'.Normal := ⟨fun x hx g => ⟨Normal.conj_mem inferInstance x hx.fst g, by
    have h1 := hVinv (QuotientGroup.mk' Q g) _ hx.snd
    rwa [hsm] at h1⟩⟩
  have hV'e : IsElementaryAbelian p V' :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext
        (mem_centralizer_iff.1 (hV'Z b.2) a (hV'Q a.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (by
        have h1 : p • Additive.ofMul (⟨x, x.2.fst⟩ : Z) = 0 := x.2.snd.2
        have h2 := congrArg (fun w : Additive Z => ((w.toMul : Z) : G)) h1
        exact h2) }
  have hV'card : Nat.card V' = Nat.card V := Nat.card_congr
    { toFun := fun x => ⟨Additive.ofMul ⟨x, x.2.fst⟩, x.2.snd⟩
      invFun := fun v => ⟨((Additive.toMul (v : Additive Z) : Z) : G),
        (Additive.toMul (v : Additive Z)).2, v.2⟩
      left_inv := fun x => rfl
      right_inv := fun v => rfl }
  have hV3 : Nat.card V < p ^ 3 := by
    by_contra hge
    push Not at hge
    obtain ⟨⟨h, hhH⟩, hh1⟩ := (ne_bot_iff_exists_ne_one).1 hHne
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q h
    obtain ⟨x, ⟨hxZ, hxV⟩, hx1, hxA, hgxA⟩ :=
      exists_mem_inf_conj (P := (P : Subgroup G)) hQA hV'Q hV'Z hAmax hPb g
        (by rw [hV'card]; exact hge)
    have hcent : ∀ y : G, y ∈ Z → y ∈ A → ∀ z ∈ (P : Subgroup G), z * y = y * z := by
      intro y hyZ hyA
      have hle : (P : Subgroup G) ≤ centralizer ({y} : Set G) := by
        rw [← hQA]
        refine sup_le (fun z hz => mem_centralizer_singleton_iff.2 ?_)
          (fun z hz => mem_centralizer_singleton_iff.2 ?_)
        · exact mem_centralizer_iff.1 hyZ z hz
        · exact congrArg Subtype.val (mul_comm' (⟨z, hz⟩ : A) ⟨y, hyA⟩)
      exact fun z hz => mem_centralizer_singleton_iff.1 (hle hz)
    have hgxZ : g⁻¹ * x * g ∈ Z := by
      have h1 := Normal.conj_mem (inferInstance : Z.Normal) x hxZ g⁻¹
      rwa [inv_inv] at h1
    have hPx := hcent x hxZ hxA
    have hPgx := hcent _ hgxZ hgxA
    refine false_of_fixed_conj hirr hnt (v := Additive.ofMul (⟨x, hxZ⟩ : Z)) ?_ ?_ hhH ?_ ?_
    · by_contra hcon
      push Not at hcon
      exact hx1 (congrArg (fun w : Additive Z => ((w.toMul : Z) : G)) (hCV _ hxV hcon))
    · rintro _ ⟨y, hy, rfl⟩
      rw [hsm]
      exact congrArg Additive.ofMul (Subtype.ext (by
        change y * x * y⁻¹ = x
        rw [hPx y hy, mul_inv_cancel_right]))
    · exact fun h0 => hh1 (Subtype.ext h0)
    · rintro _ ⟨y, hy, rfl⟩
      rw [← map_inv (QuotientGroup.mk' Q), ← map_mul (QuotientGroup.mk' Q),
        ← map_mul (QuotientGroup.mk' Q), hsm]
      refine congrArg Additive.ofMul (Subtype.ext ?_)
      change g * y * g⁻¹ * x * (g * y * g⁻¹)⁻¹ = x
      have h1 : y * (g⁻¹ * x * g) = g⁻¹ * x * g * y := hPgx y hy
      calc g * y * g⁻¹ * x * (g * y * g⁻¹)⁻¹ = g * (y * (g⁻¹ * x * g)) * y⁻¹ * g⁻¹ := by
            group
        _ = g * (g⁻¹ * x * g * y) * y⁻¹ * g⁻¹ := by rw [h1]
        _ = x := by group
  have hVcard : Nat.card V = p ∨ Nat.card V = p ^ 2 := by
    have hVdvd : Nat.card V ∣ p ^ k := hcardZ ▸ AddSubgroup.card_addSubgroup_dvd_card V
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).1 hVdvd
    rw [hj] at hV3 ⊢
    have hj3 : j < 3 := (Nat.pow_lt_pow_iff_right hp.out.one_lt).1 hV3
    have hj1 : 1 ≤ j := by
      by_contra h0
      have hj0 : j = 0 := by omega
      obtain ⟨v, hv, hv0⟩ := hVne
      have h1 : V = ⊥ := AddSubgroup.eq_bot_of_card_eq V (by rw [hj, hj0, pow_zero])
      rw [h1, AddSubgroup.mem_bot] at hv
      exact hv0 hv
    interval_cases j
    · exact Or.inl (pow_one p)
    · exact Or.inr rfl
  exact false_of_card_eq_prime_or_sq (q := q) hp2 hPb hirr hnt V hVinv hCV hVcard

end CFSG.GroupTheory.SteinbergBS
