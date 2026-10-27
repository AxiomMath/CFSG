module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36J

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {S : Sig36 X t J n e E D}

theorem PumpE.mem_of_mem_normalizer_pair {e₀ : X} {L₀ F N : Subgroup X} {r : ℕ}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin r)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin r)} {τ' : Perm (Fin r)} {DN : Finset (Fin r)}
    (P : S.PumpE e₀ L₀ F N r θN ρN τ' DN) (hr6 : 6 ≤ r) (ht2 : t * t = 1)
    (hte₀ : t ∈ centralizer ({e₀} : Set X)) (hNt : N.map (MulAut.conj t).toMonoidHom ≠ N)
    {H : Subgroup X} (hNH : N ≤ H) (htH : t ∈ H) (hFH : normalizer (F : Set X) ≤ H)
    (hL₀H : L₀ ≤ H)
    (hOC : (pPrimeCore 2 ↥(centralizer ({e₀} : Set X))).map (centralizer ({e₀} : Set X)).subtype ≤
      H)
    {y : X} (hyN : y ∈ normalizer (N : Set X))
    (hyNt : y ∈ normalizer ((N.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X)) :
    y ∈ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({e₀} : Set X) with hCdef
  set O := (pPrimeCore 2 ↥C).map C.subtype with hOdef
  set Nt := N.map (MulAut.conj t).toMonoidHom with hNtdef
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj P.NC P.Npc hte₀
  have hNtK : Nt ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne P.NC hNtC P.Npc hNtpc (Ne.symm hNt)
  have hNKt : N ≤ UnbalancedLayer.coreActionKernel Nt :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNtC P.NC hNtpc P.Npc hNt
  have hNtN : Nt ≤ normalizer (N : Set X) := fun z hz => (hNtK hz).1
  have hNNt : N ≤ normalizer (Nt : Set X) := fun z hz => (hNKt hz).1
  have hFN : F ≤ normalizer (N : Set X) := P.FL₀.trans P.L₀NN
  have hFC : F ≤ C := P.FL₀.trans (P.L₀C.trans inf_le_right)
  have hFt : F ≤ centralizer ({t} : Set X) := P.FL₀.trans (P.L₀C.trans inf_le_left)
  have hON : coreNOf N ≤ O := pPrimeCore_le_of_isPComponent P.NC P.Npc
  have hρ1 : ∀ (z : X) (hz : z ∈ Nt), ρN ⟨z, hNtN hz⟩ = 1 := fun z hz =>
    P.perm.eq_one_of_mem_coreActionKernel (by omega) (hNtK hz)
  have hker : ∀ (z : X) (hz : z ∈ N), ρN ⟨z, le_normalizer hz⟩ = 1 → z ∈ coreNOf N := by
    intro z hz h1
    rw [P.perm.apply_of_mem (by omega) ⟨z, hz⟩] at h1
    have h2 : θN ((⟨z, hz⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 := Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h2
    exact ⟨⟨z, hz⟩, h2, rfl⟩
  have hconjN : ∀ z ∈ N, t⁻¹ * z * t ∈ Nt := fun z hz =>
    ⟨z, hz, show t * z * t⁻¹ = t⁻¹ * z * t by rw [ht']⟩
  have hconjNt : ∀ z ∈ Nt, t⁻¹ * z * t ∈ N := by
    rintro _ ⟨z, hz, rfl⟩
    change t⁻¹ * (t * z * t⁻¹) * t ∈ N
    rwa [show t⁻¹ * (t * z * t⁻¹) * t = z by group]
  have hOt : ∀ z ∈ O, t * z * t⁻¹ ∈ O := fun z hz =>
    (mem_normalizer_iff.mp (le_normalizer_pPrimeCore (le_normalizer hte₀)) z).mp hz
  have hkerNN : ∀ x ∈ N ⊔ Nt, ∀ (hx : x ∈ normalizer (N : Set X))
      (hx' : t⁻¹ * x * t ∈ normalizer (N : Set X)), ρN ⟨x, hx⟩ = 1 →
      ρN ⟨t⁻¹ * x * t, hx'⟩ = 1 → x ∈ O := by
    intro x hxNN hx hx' h1 h2
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ hNNt] at hxNN
    obtain ⟨a, ha, b, hb, rfl⟩ := hxNN
    have hρa : ρN ⟨a, le_normalizer ha⟩ = 1 := by
      have e1 : (⟨a * b, hx⟩ : ↥(normalizer (N : Set X))) =
          ⟨a, le_normalizer ha⟩ * ⟨b, hNtN hb⟩ := rfl
      rw [e1, map_mul, hρ1 b hb, mul_one] at h1
      exact h1
    have hρb : ρN ⟨t⁻¹ * b * t, le_normalizer (hconjNt b hb)⟩ = 1 := by
      have e2 : (⟨t⁻¹ * (a * b) * t, hx'⟩ : ↥(normalizer (N : Set X))) =
          ⟨t⁻¹ * a * t, hNtN (hconjN a ha)⟩ * ⟨t⁻¹ * b * t, le_normalizer (hconjNt b hb)⟩ :=
        Subtype.ext (by change t⁻¹ * (a * b) * t = t⁻¹ * a * t * (t⁻¹ * b * t); group)
      rw [e2, map_mul, hρ1 _ (hconjN a ha), one_mul] at h2
      exact h2
    have haO : a ∈ O := hON (hker a ha hρa)
    have hbO : t⁻¹ * b * t ∈ O := hON (hker _ (hconjNt b hb) hρb)
    have hbO' : b ∈ O := by
      have h3 := hOt _ hbO
      rwa [show t * (t⁻¹ * b * t) * t⁻¹ = b by group] at h3
    exact mul_mem haO hbO'
  have hmatch : ∀ z (hz : z ∈ normalizer (N : Set X)), ∃ a ∈ N, ∀ (f : X) (hf : f ∈ F)
      (hw : a * z * f * z⁻¹ * a⁻¹ ∈ normalizer (N : Set X)),
      ρN ⟨a * z * f * z⁻¹ * a⁻¹, hw⟩ = ρN ⟨f, hFN hf⟩ := by
    intro z hz
    set π := ρN ⟨z, hz⟩ with hπdef
    have hDNc : 1 < (DNᶜ).card := by
      rw [Finset.card_compl, Fintype.card_fin, P.DN4]
      omega
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hDNc
    rw [Finset.mem_compl] at hu hv
    have hcF : ∀ (f : X) (hf : f ∈ F),
        swap u v * ρN ⟨f, hFN hf⟩ = ρN ⟨f, hFN hf⟩ * swap u v := by
      intro f hf
      refine (Perm.Disjoint.commute fun w => ?_).eq
      by_cases hw : w = u ∨ w = v
      · right
        rcases hw with rfl | rfl
        · exact P.Fsupp f hf w hu
        · exact P.Fsupp f hf w hv
      · left
        push Not at hw
        exact swap_apply_of_ne_of_ne hw.1 hw.2
    obtain ⟨σ, hσA, hσπ⟩ : ∃ σ : Perm (Fin r), σ ∈ alternatingGroup (Fin r) ∧
        (σ * π = 1 ∨ σ * π = swap u v) := by
      rcases Int.units_eq_one_or (Perm.sign π) with hs | hs
      · exact ⟨π⁻¹, by rw [Perm.mem_alternatingGroup, map_inv, hs, inv_one],
          Or.inl (inv_mul_cancel π)⟩
      · refine ⟨swap u v * π⁻¹, ?_, Or.inr (by group)⟩
        rw [Perm.mem_alternatingGroup, map_mul, map_inv, hs, Perm.sign_swap huv]
        decide
    obtain ⟨q, hq⟩ := θN.surjective ⟨σ, hσA⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    have ha : ρN ⟨a, le_normalizer a.2⟩ = σ := by
      rw [P.perm.apply_of_mem (by omega) a, hq]
    refine ⟨a, a.2, fun f hf hw => ?_⟩
    have e1 : (⟨(a : X) * z * f * z⁻¹ * (a : X)⁻¹, hw⟩ : ↥(normalizer (N : Set X))) =
        ⟨a, le_normalizer a.2⟩ * ⟨z, hz⟩ * ⟨f, hFN hf⟩ * (⟨z, hz⟩)⁻¹ *
          (⟨a, le_normalizer a.2⟩)⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, ha, ← hπdef]
    rcases hσπ with h | h
    · calc σ * π * ρN ⟨f, hFN hf⟩ * π⁻¹ * σ⁻¹ =
          (σ * π) * ρN ⟨f, hFN hf⟩ * (σ * π)⁻¹ := by group
        _ = ρN ⟨f, hFN hf⟩ := by rw [h]; group
    · calc σ * π * ρN ⟨f, hFN hf⟩ * π⁻¹ * σ⁻¹ =
          (σ * π) * ρN ⟨f, hFN hf⟩ * (σ * π)⁻¹ := by group
        _ = swap u v * ρN ⟨f, hFN hf⟩ * (swap u v)⁻¹ := by rw [h]
        _ = ρN ⟨f, hFN hf⟩ := by rw [hcF f hf]; group
  have hy'N : t⁻¹ * y * t ∈ normalizer (N : Set X) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := (mem_normalizer_iff.mp hyNt (t * z * t⁻¹)).mp ⟨z, hz, rfl⟩
      have h2 := hconjNt _ h1
      rwa [show t⁻¹ * (y * (t * z * t⁻¹) * y⁻¹) * t = t⁻¹ * y * t * z * (t⁻¹ * y * t)⁻¹ by
        group] at h2
    · intro hz
      have h1 : t * (t⁻¹ * y * t * z * (t⁻¹ * y * t)⁻¹) * t⁻¹ ∈ Nt := by
        have h0 := hconjN _ hz
        rw [ht'] at h0 ⊢
        exact h0
      rw [show t * (t⁻¹ * y * t * z * (t⁻¹ * y * t)⁻¹) * t⁻¹ = y * (t * z * t⁻¹) * y⁻¹ by
        group] at h1
      have h2 := (mem_normalizer_iff.mp hyNt (t * z * t⁻¹)).mpr h1
      have h3 := hconjNt _ h2
      rwa [show t⁻¹ * (t * z * t⁻¹) * t = z by group] at h3
  obtain ⟨a, haN, ha⟩ := hmatch y hyN
  obtain ⟨b', hb'N, hb'⟩ := hmatch _ hy'N
  set b := t * b' * t⁻¹ with hbdef
  have hbNt : b ∈ Nt := ⟨b', hb'N, rfl⟩
  have hNtH : Nt ≤ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
  have hjH : b * a ∈ H := mul_mem (hNtH hbNt) (hNH haN)
  have hNNtN : N ⊔ Nt ≤ normalizer (N : Set X) := sup_le le_normalizer hNtN
  have hjN : b * a ∈ N ⊔ Nt := mul_mem (mem_sup_right hbNt) (mem_sup_left haN)
  have hyNN : y ∈ normalizer ((N ⊔ Nt : Subgroup X) : Set X) := sup_mem_normalizer hyN hyNt
  have hjyNN : b * a * y ∈ normalizer ((N ⊔ Nt : Subgroup X) : Set X) :=
    mul_mem (le_normalizer hjN) hyNN
  have hFNN : F ≤ N ⊔ Nt := P.FL₀.trans P.L₀N
  have hw : ∀ f ∈ F, (b * a * y) * f * (b * a * y)⁻¹ * f⁻¹ ∈ O := by
    intro f hf
    have hft : t⁻¹ * f * t = f := by
      have h1 : f * t = t * f := mem_centralizer_singleton_iff.mp (hFt hf)
      rw [mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
    have hwNN : (b * a * y) * f * (b * a * y)⁻¹ * f⁻¹ ∈ N ⊔ Nt :=
      mul_mem ((mem_normalizer_iff.mp hjyNN f).mp (hFNN hf)) (inv_mem (hFNN hf))
    have hid : t⁻¹ * ((b * a * y) * f * (b * a * y)⁻¹ * f⁻¹) * t =
        b' * (t⁻¹ * a * t) * (t⁻¹ * y * t * f * (t⁻¹ * y * t)⁻¹) * (t⁻¹ * a * t)⁻¹ * b'⁻¹ *
          f⁻¹ := by
      have h0 : t⁻¹ * ((b * a * y) * f * (b * a * y)⁻¹ * f⁻¹) * t =
          b' * (t⁻¹ * a * t) * (t⁻¹ * y * t * (t⁻¹ * f * t) * (t⁻¹ * y * t)⁻¹) *
            (t⁻¹ * a * t)⁻¹ * b'⁻¹ * (t⁻¹ * f * t)⁻¹ := by
        rw [hbdef]
        group
      rw [hft] at h0
      exact h0
    have hwt : t⁻¹ * ((b * a * y) * f * (b * a * y)⁻¹ * f⁻¹) * t ∈ normalizer (N : Set X) := by
      rw [hid]
      refine mul_mem (mul_mem (mul_mem (mul_mem (mul_mem (le_normalizer hb'N)
        (hNtN (hconjN a haN))) ?_) (inv_mem (hNtN (hconjN a haN)))) (inv_mem
        (le_normalizer hb'N))) (inv_mem (hFN hf))
      exact mul_mem (mul_mem hy'N (hFN hf)) (inv_mem hy'N)
    refine hkerNN _ hwNN (hNNtN hwNN) hwt ?_ ?_
    · have e1 : (⟨(b * a * y) * f * (b * a * y)⁻¹ * f⁻¹, hNNtN hwNN⟩ :
          ↥(normalizer (N : Set X))) = ⟨b, hNtN hbNt⟩ *
            ⟨a * y * f * y⁻¹ * a⁻¹, mul_mem (mul_mem (mul_mem (mul_mem (le_normalizer haN) hyN)
              (hFN hf)) (inv_mem hyN)) (inv_mem (le_normalizer haN))⟩ *
            (⟨b, hNtN hbNt⟩)⁻¹ * (⟨f, hFN hf⟩)⁻¹ := by
        apply Subtype.ext
        change (b * a * y) * f * (b * a * y)⁻¹ * f⁻¹ = b * (a * y * f * y⁻¹ * a⁻¹) * b⁻¹ * f⁻¹
        group
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hρ1 b hbNt, ha f hf]
      group
    · have e2 : (⟨t⁻¹ * ((b * a * y) * f * (b * a * y)⁻¹ * f⁻¹) * t, hwt⟩ :
          ↥(normalizer (N : Set X))) = ⟨b', le_normalizer hb'N⟩ *
            ⟨t⁻¹ * a * t, hNtN (hconjN a haN)⟩ *
            ⟨t⁻¹ * y * t * f * (t⁻¹ * y * t)⁻¹,
              mul_mem (mul_mem hy'N (hFN hf)) (inv_mem hy'N)⟩ *
            (⟨t⁻¹ * a * t, hNtN (hconjN a haN)⟩)⁻¹ * (⟨b', le_normalizer hb'N⟩)⁻¹ *
            (⟨f, hFN hf⟩)⁻¹ := by
        apply Subtype.ext
        exact hid
      have hb'f := hb' f hf (mul_mem (mul_mem (mul_mem (mul_mem (le_normalizer hb'N) hy'N)
        (hFN hf)) (inv_mem hy'N)) (inv_mem (le_normalizer hb'N)))
      have e3 : (⟨b' * (t⁻¹ * y * t) * f * (t⁻¹ * y * t)⁻¹ * b'⁻¹, mul_mem (mul_mem (mul_mem
          (mul_mem (le_normalizer hb'N) hy'N) (hFN hf)) (inv_mem hy'N))
          (inv_mem (le_normalizer hb'N))⟩ : ↥(normalizer (N : Set X))) =
          ⟨b', le_normalizer hb'N⟩ * ⟨t⁻¹ * y * t * f * (t⁻¹ * y * t)⁻¹,
            mul_mem (mul_mem hy'N (hFN hf)) (inv_mem hy'N)⟩ * (⟨b', le_normalizer hb'N⟩)⁻¹ := by
        apply Subtype.ext
        change b' * (t⁻¹ * y * t) * f * (t⁻¹ * y * t)⁻¹ * b'⁻¹ =
          b' * (t⁻¹ * y * t * f * (t⁻¹ * y * t)⁻¹) * b'⁻¹
        group
      rw [e3, map_mul, map_mul, map_inv] at hb'f
      rw [e2, map_mul, map_mul, map_mul, map_mul, map_mul, map_inv, map_inv, map_inv,
        hρ1 _ (hconjN a haN)]
      calc ρN ⟨b', le_normalizer hb'N⟩ * 1 * ρN ⟨t⁻¹ * y * t * f * (t⁻¹ * y * t)⁻¹,
            mul_mem (mul_mem hy'N (hFN hf)) (inv_mem hy'N)⟩ * 1⁻¹ *
            (ρN ⟨b', le_normalizer hb'N⟩)⁻¹ * (ρN ⟨f, hFN hf⟩)⁻¹ =
          ρN ⟨b', le_normalizer hb'N⟩ * ρN ⟨t⁻¹ * y * t * f * (t⁻¹ * y * t)⁻¹,
            mul_mem (mul_mem hy'N (hFN hf)) (inv_mem hy'N)⟩ *
            (ρN ⟨b', le_normalizer hb'N⟩)⁻¹ * (ρN ⟨f, hFN hf⟩)⁻¹ := by group
        _ = 1 := by rw [hb'f]; group
  have hFO : F ≤ normalizer (O : Set X) := fun f hf =>
    le_normalizer_pPrimeCore (le_normalizer (hFC hf))
  have hF2 : IsPGroup 2 F := IsPGroup.of_card (n := 2) (by rw [P.F4]; norm_num)
  have hOodd : Odd (Nat.card O) := by
    rw [hOdef, card_map_of_injective C.subtype_injective]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hAle : F.map (MulAut.conj (b * a * y)).toMonoidHom ≤ F ⊔ O := by
    rintro _ ⟨f, hf, rfl⟩
    have h1 : (MulAut.conj (b * a * y)).toMonoidHom f =
        ((b * a * y) * f * (b * a * y)⁻¹ * f⁻¹) * f := by
      change b * a * y * f * (b * a * y)⁻¹ = _
      group
    rw [h1]
    exact mul_mem (mem_sup_right (hw f hf)) (mem_sup_left hf)
  obtain ⟨k, hk, hkF⟩ := exists_conj_of_le_sup_odd' hFO hF2 hOodd hAle
    (card_map_of_injective (MulAut.conj (b * a * y)).injective)
  have hkN : k * (b * a * y) ∈ normalizer (F : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change F.map (MulAut.conj (k * (b * a * y))).toMonoidHom = F
    rw [map_conj_mul]
    exact hkF
  have hkH : k ∈ H := (sup_le (P.FL₀.trans hL₀H) hOC) hk
  have h1 := mul_mem (inv_mem (mul_mem hkH hjH)) (hFH hkN)
  rwa [show (k * (b * a))⁻¹ * (k * (b * a * y)) = y by group] at h1

end Sig36

end CFSG.ComponentClassification.SolMax
