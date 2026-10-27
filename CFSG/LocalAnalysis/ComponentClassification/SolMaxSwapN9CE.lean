module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9CC

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

namespace SwapN9

theorem mem_of_mem_normalizer_pair_five [Finite X] {H N F : Subgroup X} {t e₀ h y : X}
    {θN : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin 5)}
    {ρN : ↥(normalizer (N : Set X)) →* Perm (Fin 5)} (hρ : IsPermAction θN ρN)
    (ht2 : t * t = 1) (hte₀ : t ∈ centralizer ({e₀} : Set X))
    (hNC : N ≤ centralizer ({e₀} : Set X))
    (hNpc : IsPComponent 2 (N.subgroupOf (centralizer ({e₀} : Set X))))
    (hNt : N.map (MulAut.conj t).toMonoidHom ≠ N) (hNH : N ≤ H) (htH : t ∈ H)
    (hFH : normalizer (F : Set X) ≤ H) (hOC : coreNOf (centralizer ({e₀} : Set X)) ≤ H)
    (hFNN : F ≤ N ⊔ N.map (MulAut.conj t).toMonoidHom) (hF2 : IsPGroup 2 F)
    (hFC : F ≤ centralizer ({e₀} : Set X))
    (hhH : h ∈ H) (hhN : h ∈ normalizer (N : Set X))
    (hhNt : h ∈ normalizer ((N.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X))
    (hhodd : Perm.sign (ρN ⟨h, hhN⟩) = -1)
    (hhK : t⁻¹ * h * t ∈ UnbalancedLayer.coreActionKernel N)
    (hyN : y ∈ normalizer (N : Set X))
    (hyNt : y ∈ normalizer ((N.map (MulAut.conj t).toMonoidHom : Subgroup X) : Set X)) :
    y ∈ H := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({e₀} : Set X) with hCdef
  set O := (pPrimeCore 2 ↥C).map C.subtype with hOdef
  set Nt := N.map (MulAut.conj t).toMonoidHom with hNtdef
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨hNtC, hNtpc⟩ := isPComponent_conj hNC hNpc hte₀
  have hNtK : Nt ≤ UnbalancedLayer.coreActionKernel N :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNC hNtC hNpc hNtpc (Ne.symm hNt)
  have hNKt : N ≤ UnbalancedLayer.coreActionKernel Nt :=
    GSThmB.B5a.le_coreActionKernel_of_ne hNtC hNC hNtpc hNpc hNt
  have hNtN : Nt ≤ normalizer (N : Set X) := fun z hz => (hNtK hz).1
  have hNNt : N ≤ normalizer (Nt : Set X) := fun z hz => (hNKt hz).1
  have hON : coreNOf N ≤ O := pPrimeCore_le_of_isPComponent hNC hNpc
  have hρ1 : ∀ (z : X) (hz : z ∈ Nt), ρN ⟨z, hNtN hz⟩ = 1 := fun z hz =>
    hρ.eq_one_of_mem_coreActionKernel (by norm_num) (hNtK hz)
  have hker : ∀ (z : X) (hz : z ∈ N), ρN ⟨z, le_normalizer hz⟩ = 1 → z ∈ coreNOf N := by
    intro z hz h1
    rw [hρ.apply_of_mem (by norm_num) ⟨z, hz⟩] at h1
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
  have hconjNorm : ∀ z, z ∈ normalizer (Nt : Set X) → t⁻¹ * z * t ∈ normalizer (N : Set X) := by
    intro z hz
    rw [mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h1 := (mem_normalizer_iff.mp hz (t * w * t⁻¹)).mp ⟨w, hw, rfl⟩
      have h2 := hconjNt _ h1
      rwa [show t⁻¹ * (z * (t * w * t⁻¹) * z⁻¹) * t = t⁻¹ * z * t * w * (t⁻¹ * z * t)⁻¹ by
        group] at h2
    · intro hw
      have h1 : t * (t⁻¹ * z * t * w * (t⁻¹ * z * t)⁻¹) * t⁻¹ ∈ Nt := by
        have h0 := hconjN _ hw
        rw [ht'] at h0 ⊢
        exact h0
      rw [show t * (t⁻¹ * z * t * w * (t⁻¹ * z * t)⁻¹) * t⁻¹ = z * (t * w * t⁻¹) * z⁻¹ by
        group] at h1
      have h2 := (mem_normalizer_iff.mp hz (t * w * t⁻¹)).mpr h1
      have h3 := hconjNt _ h2
      rwa [show t⁻¹ * (t * w * t⁻¹) * t = w by group] at h3
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
  have hNtH : Nt ≤ H := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem htH (hNH hz)) (inv_mem htH)
  have hFNNt : F ≤ normalizer (N : Set X) := hFNN.trans (sup_le le_normalizer hNtN)
  have hFH' : F ≤ H := hFNN.trans (sup_le hNH hNtH)
  have hmain : ∀ y' (hy'N : y' ∈ normalizer (N : Set X)) (hy'Nt : y' ∈ normalizer (Nt : Set X)),
      Perm.sign (ρN ⟨y', hy'N⟩) = 1 →
      Perm.sign (ρN ⟨t⁻¹ * y' * t, hconjNorm y' hy'Nt⟩) = 1 → y' ∈ H := by
    intro y' hy'N hy'Nt hs1 hs2
    obtain ⟨q₁, hq₁⟩ := θN.surjective ⟨ρN ⟨y', hy'N⟩, by rw [Perm.mem_alternatingGroup]; exact hs1⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q₁
    have hρa : ρN ⟨a, le_normalizer a.2⟩ = ρN ⟨y', hy'N⟩ := by
      rw [hρ.apply_of_mem (by norm_num) a, hq₁]
    obtain ⟨q₂, hq₂⟩ := θN.surjective
      ⟨ρN ⟨t⁻¹ * y' * t, hconjNorm y' hy'Nt⟩, by rw [Perm.mem_alternatingGroup]; exact hs2⟩
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective q₂
    have hρb' : ρN ⟨b', le_normalizer b'.2⟩ = ρN ⟨t⁻¹ * y' * t, hconjNorm y' hy'Nt⟩ := by
      rw [hρ.apply_of_mem (by norm_num) b', hq₂]
    set b := t * (b' : X) * t⁻¹ with hbdef
    have hbNt : b ∈ Nt := ⟨b', b'.2, rfl⟩
    set y'' := b⁻¹ * (a : X)⁻¹ * y' with hy''def
    have hy''N : y'' ∈ normalizer (N : Set X) :=
      mul_mem (mul_mem (inv_mem (hNtN hbNt)) (inv_mem (le_normalizer a.2))) hy'N
    have hy''Nt : y'' ∈ normalizer (Nt : Set X) :=
      mul_mem (mul_mem (inv_mem (le_normalizer hbNt)) (inv_mem (hNNt a.2))) hy'Nt
    have hρy'' : ρN ⟨y'', hy''N⟩ = 1 := by
      have e1 : (⟨y'', hy''N⟩ : ↥(normalizer (N : Set X))) = (⟨b, hNtN hbNt⟩)⁻¹ *
          (⟨a, le_normalizer a.2⟩)⁻¹ * ⟨y', hy'N⟩ := rfl
      rw [e1, map_mul, map_mul, map_inv, map_inv, hρ1 b hbNt, hρa]
      group
    have hρy''t : ρN ⟨t⁻¹ * y'' * t, hconjNorm y'' hy''Nt⟩ = 1 := by
      have hbt : t⁻¹ * b * t = b' := by rw [hbdef]; group
      have e1 : (⟨t⁻¹ * y'' * t, hconjNorm y'' hy''Nt⟩ : ↥(normalizer (N : Set X))) =
          (⟨b', le_normalizer b'.2⟩)⁻¹ * (⟨t⁻¹ * a * t, hNtN (hconjN a a.2)⟩)⁻¹ *
            ⟨t⁻¹ * y' * t, hconjNorm y' hy'Nt⟩ := by
        apply Subtype.ext
        change t⁻¹ * (b⁻¹ * (a : X)⁻¹ * y') * t = (b' : X)⁻¹ * (t⁻¹ * a * t)⁻¹ * (t⁻¹ * y' * t)
        rw [← hbt]
        group
      rw [e1, map_mul, map_mul, map_inv, map_inv, hρ1 _ (hconjN a a.2), hρb']
      group
    have hyNN : y'' ∈ normalizer ((N ⊔ Nt : Subgroup X) : Set X) := sup_mem_normalizer hy''N hy''Nt
    have hw : ∀ f ∈ F, y'' * f * y''⁻¹ * f⁻¹ ∈ O := by
      intro f hf
      have hfN : f ∈ normalizer (N : Set X) := hFNNt hf
      have hfNt : f ∈ normalizer (Nt : Set X) := (sup_le hNNt le_normalizer) (hFNN hf)
      have hwNN : y'' * f * y''⁻¹ * f⁻¹ ∈ N ⊔ Nt :=
        mul_mem ((mem_normalizer_iff.mp hyNN f).mp (hFNN hf)) (inv_mem (hFNN hf))
      have hwN : y'' * f * y''⁻¹ * f⁻¹ ∈ normalizer (N : Set X) :=
        mul_mem (mul_mem (mul_mem hy''N hfN) (inv_mem hy''N)) (inv_mem hfN)
      have hwNt' : t⁻¹ * (y'' * f * y''⁻¹ * f⁻¹) * t ∈ normalizer (N : Set X) := by
        have h1 : t⁻¹ * (y'' * f * y''⁻¹ * f⁻¹) * t = (t⁻¹ * y'' * t) * (t⁻¹ * f * t) *
            (t⁻¹ * y'' * t)⁻¹ * (t⁻¹ * f * t)⁻¹ := by group
        rw [h1]
        exact mul_mem (mul_mem (mul_mem (hconjNorm y'' hy''Nt) (hconjNorm f hfNt))
          (inv_mem (hconjNorm y'' hy''Nt))) (inv_mem (hconjNorm f hfNt))
      refine hkerNN _ hwNN hwN hwNt' ?_ ?_
      · have e1 : (⟨y'' * f * y''⁻¹ * f⁻¹, hwN⟩ : ↥(normalizer (N : Set X))) =
            ⟨y'', hy''N⟩ * ⟨f, hfN⟩ * (⟨y'', hy''N⟩)⁻¹ * (⟨f, hfN⟩)⁻¹ := rfl
        rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hρy'']
        group
      · have e1 : (⟨t⁻¹ * (y'' * f * y''⁻¹ * f⁻¹) * t, hwNt'⟩ : ↥(normalizer (N : Set X))) =
            ⟨t⁻¹ * y'' * t, hconjNorm y'' hy''Nt⟩ * ⟨t⁻¹ * f * t, hconjNorm f hfNt⟩ *
              (⟨t⁻¹ * y'' * t, hconjNorm y'' hy''Nt⟩)⁻¹ *
              (⟨t⁻¹ * f * t, hconjNorm f hfNt⟩)⁻¹ := by
          apply Subtype.ext
          change t⁻¹ * (y'' * f * y''⁻¹ * f⁻¹) * t = (t⁻¹ * y'' * t) * (t⁻¹ * f * t) *
            (t⁻¹ * y'' * t)⁻¹ * (t⁻¹ * f * t)⁻¹
          group
        rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hρy''t]
        group
    have hFO : F ≤ normalizer (O : Set X) := fun f hf =>
      le_normalizer_pPrimeCore (le_normalizer (hFC hf))
    have hOodd : Odd (Nat.card O) := by
      rw [hOdef, card_map_of_injective C.subtype_injective]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    have hAle : F.map (MulAut.conj y'').toMonoidHom ≤ F ⊔ O := by
      rintro _ ⟨f, hf, rfl⟩
      have h1 : (MulAut.conj y'').toMonoidHom f = (y'' * f * y''⁻¹ * f⁻¹) * f := by
        change y'' * f * y''⁻¹ = _
        group
      rw [h1]
      exact mul_mem (mem_sup_right (hw f hf)) (mem_sup_left hf)
    obtain ⟨k, hk, hkF⟩ := exists_conj_of_le_sup_odd' hFO hF2 hOodd hAle
      (card_map_of_injective (MulAut.conj y'').injective)
    have hkN : k * y'' ∈ normalizer (F : Set X) := by
      rw [mem_normalizer_iff_map_conj_eq]
      change F.map (MulAut.conj (k * y'')).toMonoidHom = F
      rw [map_conj_mul]
      exact hkF
    have hkH : k ∈ H := (sup_le hFH' hOC) hk
    have hy''H : y'' ∈ H := by
      have h1 := mul_mem (inv_mem hkH) (hFH hkN)
      rwa [show k⁻¹ * (k * y'') = y'' by group] at h1
    have h2 := mul_mem (mul_mem (hNH a.2) (hNtH hbNt)) hy''H
    rwa [show (a : X) * b * y'' = y' by rw [hy''def]; group] at h2
  set h' := t * h * t⁻¹ with hh'def
  have hh'eq : h' = t⁻¹ * h * t := by rw [hh'def, ht']
  have hh'N : h' ∈ normalizer (N : Set X) := by rw [hh'eq]; exact hhK.1
  have hh'Nt : h' ∈ normalizer (Nt : Set X) := by
    rw [mem_normalizer_iff_map_conj_eq]
    change Nt.map (MulAut.conj h').toMonoidHom = Nt
    have hhN' : N.map (MulAut.conj h).toMonoidHom = N := mem_normalizer_iff_map_conj_eq.mp hhN
    rw [hNtdef, map_conj_map_conj, hh'def, show t * h * t⁻¹ * t = t * h by group,
      ← map_conj_map_conj, hhN']
  have hh'H : h' ∈ H := mul_mem (mul_mem htH hhH) (inv_mem htH)
  have hρh' : ρN ⟨h', hh'N⟩ = 1 := by
    have h1 := hρ.eq_one_of_mem_coreActionKernel (by norm_num) hhK
    have h2 : (⟨h', hh'N⟩ : ↥(normalizer (N : Set X))) = ⟨t⁻¹ * h * t, hhK.1⟩ :=
      Subtype.ext hh'eq
    rw [h2]
    exact h1
  have hρh't : ρN ⟨t⁻¹ * h' * t, hconjNorm h' hh'Nt⟩ = ρN ⟨h, hhN⟩ := by
    congr 1
    apply Subtype.ext
    change t⁻¹ * (t * h * t⁻¹) * t = h
    group
  have hρht : ρN ⟨t⁻¹ * h * t, hconjNorm h hhNt⟩ = 1 :=
    hρ.eq_one_of_mem_coreActionKernel (by norm_num) hhK
  have hsgn : ∀ (u v : X) (hu : u ∈ normalizer (N : Set X)) (hv : v ∈ normalizer (N : Set X)),
      Perm.sign (ρN ⟨u * v, mul_mem hu hv⟩) = Perm.sign (ρN ⟨u, hu⟩) * Perm.sign (ρN ⟨v, hv⟩) := by
    intro u v hu hv
    have e1 : (⟨u * v, mul_mem hu hv⟩ : ↥(normalizer (N : Set X))) = ⟨u, hu⟩ * ⟨v, hv⟩ := rfl
    rw [e1, map_mul, map_mul]
  have hconjmul : ∀ (u v : X) (hu : u ∈ normalizer (Nt : Set X))
      (hv : v ∈ normalizer (Nt : Set X)),
      Perm.sign (ρN ⟨t⁻¹ * (u * v) * t, hconjNorm _ (mul_mem hu hv)⟩) =
        Perm.sign (ρN ⟨t⁻¹ * u * t, hconjNorm u hu⟩) *
          Perm.sign (ρN ⟨t⁻¹ * v * t, hconjNorm v hv⟩) := by
    intro u v hu hv
    have e1 : (⟨t⁻¹ * (u * v) * t, hconjNorm _ (mul_mem hu hv)⟩ : ↥(normalizer (N : Set X))) =
        ⟨t⁻¹ * u * t, hconjNorm u hu⟩ * ⟨t⁻¹ * v * t, hconjNorm v hv⟩ := by
      apply Subtype.ext
      change t⁻¹ * (u * v) * t = t⁻¹ * u * t * (t⁻¹ * v * t)
      group
    rw [e1, map_mul, map_mul]
  have hsign1 : Perm.sign (ρN ⟨h', hh'N⟩) = 1 := by rw [hρh', map_one]
  have hsign2 : Perm.sign (ρN ⟨t⁻¹ * h * t, hconjNorm h hhNt⟩) = 1 := by rw [hρht, map_one]
  have hsign3 : Perm.sign (ρN ⟨t⁻¹ * h' * t, hconjNorm h' hh'Nt⟩) = -1 := by rw [hρh't, hhodd]
  rcases Int.units_eq_one_or (Perm.sign (ρN ⟨y, hyN⟩)) with hs | hs <;>
    rcases Int.units_eq_one_or (Perm.sign (ρN ⟨t⁻¹ * y * t, hconjNorm y hyNt⟩)) with hs' | hs'
  · exact hmain y hyN hyNt hs hs'
  · have h1 := hmain (y * h') (mul_mem hyN hh'N) (mul_mem hyNt hh'Nt)
      (by rw [hsgn y h' hyN hh'N, hs, hsign1, one_mul])
      (by rw [hconjmul y h' hyNt hh'Nt, hs', hsign3]; decide)
    have h2 := mul_mem h1 (inv_mem hh'H)
    rwa [mul_inv_cancel_right] at h2
  · have h1 := hmain (y * h) (mul_mem hyN hhN) (mul_mem hyNt hhNt)
      (by rw [hsgn y h hyN hhN, hs, hhodd]; decide)
      (by rw [hconjmul y h hyNt hhNt, hs', hsign2, one_mul])
    have h2 := mul_mem h1 (inv_mem hhH)
    rwa [mul_inv_cancel_right] at h2
  · have hyh : y * h ∈ normalizer (N : Set X) := mul_mem hyN hhN
    have hyht : y * h ∈ normalizer (Nt : Set X) := mul_mem hyNt hhNt
    have h1 := hmain (y * h * h') (mul_mem hyh hh'N) (mul_mem hyht hh'Nt)
      (by rw [hsgn (y * h) h' hyh hh'N, hsgn y h hyN hhN, hs, hhodd, hsign1]; decide)
      (by rw [hconjmul (y * h) h' hyht hh'Nt, hconjmul y h hyNt hhNt, hs', hsign2, hsign3]; decide)
    have h2 := mul_mem (mul_mem h1 (inv_mem hh'H)) (inv_mem hhH)
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at h2

end SwapN9

end CFSG.ComponentClassification.SolMax
