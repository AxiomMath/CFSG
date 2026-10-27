module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Comm
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7Rank

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  {N : Notation25 hs} {n : ℕ} {K₁ K₂ V V' : Subgroup G} {s : G}

namespace L257

theorem SC_le_S' (N : Notation25 hs) : N.SC ≤ N.S := inf_le_left

omit [Finite G] in
theorem mem_normalizer_of_commute {g : G} {Y : Subgroup G} (h : ∀ r ∈ Y, g * r = r * g) :
    g ∈ Subgroup.normalizer (Y : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · have : g * x * g⁻¹ = x := by rw [h x hx]; group
    rw [this]
    exact hx
  · have h1 := h _ hx
    have h2 : g * x * g⁻¹ = x := by
      have h3 : g * (g * x * g⁻¹) = g * x := by rw [h1]; group
      exact mul_left_cancel h3
    rw [h2] at hx
    exact hx

omit [Finite G] in
theorem orderOf_conj_inv (x h : G) : orderOf (x⁻¹ * h * x) = orderOf h := by
  have := (MulAut.conj x⁻¹).orderOf_eq h
  simpa [MulAut.conj_apply] using this

end L257

namespace Conf257

variable (c : Conf257 N n K₁ K₂ V V' s)

include c in
theorem normalizes_of_mem_borel {h : G} (hh : h ∈ N.K ⊓ Subgroup.normalizer (N.SK : Set G)) :
    CFSG.conjugate V h = V ∧ CFSG.conjugate V' h = V' ∧
      CFSG.conjugate (V ⊓ V') h = V ⊓ V' ∧ CFSG.conjugate ⁅V, V'⁆ h = ⁅V, V'⁆ := by
  have hV : CFSG.conjugate V h = V :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (c.K₁_le_normalizer_V (c.setup.pair.lt₁.le hh))
  have hV' : CFSG.conjugate V' h = V' :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr
      (c.K₂_le_normalizer_V' (c.setup.pair.lt₂.le hh))
  refine ⟨hV, hV', ?_, ?_⟩
  · rw [BenderBranch.conjugate_inf, hV, hV']
  · rw [L257.conjugate_commutator' V V' h, hV, hV']

include c in
theorem g_props {h : G} (hh : h ∈ N.K ⊓ Subgroup.normalizer (N.SK : Set G))
    (hDh : ¬ ⁅V, V'⁆ ≤ Subgroup.centralizer ({h} : Set G)) :
    N.x⁻¹ * h * N.x ∈ CFSG.conjugate N.K N.x ∧
      CFSG.conjugate (CFSG.conjugate ⁅V, V'⁆ N.x) (N.x⁻¹ * h * N.x) = CFSG.conjugate ⁅V, V'⁆ N.x ∧
      CFSG.conjugate (CFSG.conjugate (V ⊓ V') N.x) (N.x⁻¹ * h * N.x) =
        CFSG.conjugate (V ⊓ V') N.x ∧
      ¬ CFSG.conjugate ⁅V, V'⁆ N.x ≤ Subgroup.centralizer ({N.x⁻¹ * h * N.x} : Set G) := by
  obtain ⟨-, -, hD₀, hD⟩ := c.normalizes_of_mem_borel hh
  have hxg : N.x * (N.x⁻¹ * h * N.x) = h * N.x := by group
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [CFSG.QuasithinUnique.mem_conjugate_iff]
    have : N.x * (N.x⁻¹ * h * N.x) * N.x⁻¹ = h := by group
    rw [this]
    exact hh.1
  · rw [BenderBranch.conjugate_conjugate, hxg, ← BenderBranch.conjugate_conjugate, hD]
  · rw [BenderBranch.conjugate_conjugate, hxg, ← BenderBranch.conjugate_conjugate, hD₀]
  · intro hle
    apply hDh
    intro d hd
    have hmem : N.x⁻¹ * d * N.x ∈ CFSG.conjugate ⁅V, V'⁆ N.x := by
      rw [CFSG.QuasithinUnique.mem_conjugate_iff]
      have : N.x * (N.x⁻¹ * d * N.x) * N.x⁻¹ = d := by group
      rw [this]
      exact hd
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hmem)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : N.x⁻¹ * (d * h) * N.x = N.x⁻¹ * (h * d) * N.x := by
      calc N.x⁻¹ * (d * h) * N.x = N.x⁻¹ * d * N.x * (N.x⁻¹ * h * N.x) := by group
        _ = N.x⁻¹ * h * N.x * (N.x⁻¹ * d * N.x) := h1
        _ = N.x⁻¹ * (h * d) * N.x := by group
    exact mul_left_cancel (mul_right_cancel h3)

omit c in
theorem S_le_normalizer_conjugate {Y : Subgroup G} (hY : N.S ≤ Subgroup.normalizer (Y : Set G)) :
    N.S ≤ Subgroup.normalizer (CFSG.conjugate Y N.x : Set G) := by
  intro g hg
  rw [← BenderBranch.conjugate_eq_iff_mem_normalizer]
  have hg'S : N.x * g * N.x⁻¹ ∈ N.S := L257.x_conj_S N hg
  have hxg : N.x * g = (N.x * g * N.x⁻¹) * N.x := by simp [mul_assoc]
  rw [BenderBranch.conjugate_conjugate, hxg, ← BenderBranch.conjugate_conjugate,
    BenderBranch.conjugate_eq_iff_mem_normalizer.mpr (hY hg'S)]

include c in
theorem false_endgame (hlv : Lv256 N) (hA6 : ¬ Nonempty (↥N.K ≃* alternatingGroup (Fin 6))) :
    False := by
  have hint : N.SC ⊓ CFSG.conjugate N.SC N.x = ⊥ := hlv.concl255.1
  obtain ⟨E, hEdef, hEne, hERC, hESC, hSE⟩ := c.exists_E hint
  have h256 := hlv.concl256 E hEne hESC hSE
  have hcomp : IsComponentIn N.K (Subgroup.normalizer (E : Set G)) :=
    h256.2.2.resolve_right (fun h => hA6 h.2.1)
  obtain ⟨p, hp, hp2, ⟨P₀, hP₀K, hP₀, hP₀card⟩, h, hhB, ⟨k, hk⟩, hDh⟩ := c.torus
  have : Fact p.Prime := ⟨hp⟩
  have hxS : N.x ∈ Subgroup.normalizer (N.S : Set G) := N.x_mem.2
  obtain ⟨hgKx, hgE, hgD₀, hgnc⟩ := c.g_props hhB hDh
  rw [← hEdef] at hgE hgnc
  set g : G := N.x⁻¹ * h * N.x with hg
  have hgord : orderOf g = p ^ k := by rw [hg, L257.orderOf_conj_inv, hk]
  have hgNE : g ∈ Subgroup.normalizer (E : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mp hgE
  have hKN : N.K ≤ Subgroup.normalizer (E : Set G) := by
    have hKc : N.K ≤ Subgroup.centralizer (E : Set G) := fun k' hk' =>
      Subgroup.mem_centralizer_iff.mpr fun e he =>
        (Subgroup.mem_centralizer_iff.mp (c.SC_le_centralizer (hESC he)) k' hk').symm
    exact hKc.trans (Subgroup.centralizer_le_normalizer _)
  have hE2 : IsPGroup 2 E := N.tuple.sylow.isPGroup.to_le (hESC.trans (L257.SC_le_S' N))
  have hcore : pCoreOf 2 (Subgroup.normalizer (E : Set G)) ≠ ⊥ := by
    intro hbot
    have hle : E ≤ pCoreOf 2 (Subgroup.normalizer (E : Set G)) :=
      CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E _ Subgroup.le_normalizer
        ((Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl) hE2
    rw [hbot] at hle
    exact hEne (le_bot_iff.mp hle)
  have he2 : CFSG.Assembly.evenRank G ≤ 2 := hs.setting.qtke.2.2
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' p
    (show p ∣ Nat.card P₀ by rw [hP₀card]; exact dvd_pow_self p two_ne_zero)
  have hy₀G : orderOf (y₀ : G) = p := by rw [Subgroup.orderOf_coe]; exact hy₀
  have hpodd : Odd (orderOf g) := by
    rw [hgord]
    exact (hp.odd_of_ne_two hp2).pow
  have hgNK : g ∈ Subgroup.normalizer (N.K : Set G) := by
    have hKg : IsComponentIn (CFSG.conjugate N.K g) (Subgroup.normalizer (E : Set G)) :=
      Unc25G2.isComponentIn_conjugate hcomp hgNE
    rcases BenderBranch.eq_or_commute_of_isComponentIn hcomp hKg with heq | hcom
    · exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp heq.symm
    · exfalso
      have hKc : N.K ≤ Subgroup.centralizer (CFSG.conjugate N.K g : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcom
      set y : G := g⁻¹ * (y₀ : G) * g with hy
      have hyKg : y ∈ CFSG.conjugate N.K g := by
        rw [CFSG.QuasithinUnique.mem_conjugate_iff]
        have : g * y * g⁻¹ = (y₀ : G) := by rw [hy]; group
        rw [this]
        exact hP₀K y₀.2
      have hyo : orderOf y = p := by rw [hy, L257.orderOf_conj_inv, hy₀G]
      have hyN : y ∈ Subgroup.normalizer (E : Set G) :=
        (Subgroup.normalizer (E : Set G)).mul_mem
          ((Subgroup.normalizer (E : Set G)).mul_mem
            ((Subgroup.normalizer (E : Set G)).inv_mem hgNE) (hKN (hP₀K y₀.2))) hgNE
      have hyC : y ∈ Subgroup.centralizer (N.K : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun a ha =>
          (Subgroup.mem_centralizer_iff.mp (hKc ha) y hyKg).symm
      have hcomm : ∀ a ∈ P₀, a * y = y * a := fun a ha =>
        (Subgroup.mem_centralizer_iff.mp (hKc (hP₀K ha)) y hyKg).symm
      have hyP : y ∉ P₀ := by
        intro hyP
        have hyZ : y ∈ centerOf N.K := ⟨hP₀K hyP, hyC⟩
        have h2 : y ^ 2 = 1 := c.center_elem.2 y hyZ
        have hdvd : p ∣ 2 := hyo ▸ orderOf_dvd_of_pow_eq_one h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
      exact L257.cube_contradiction he2 hcore hp hp2 hP₀ hP₀card (hP₀K.trans hKN) hyN hyo hcomm
        hyP
  set D₀x : Subgroup G := CFSG.conjugate (V ⊓ V') N.x with hD₀x
  set RCx : Subgroup G := CFSG.conjugate (thompsonJ N.SC) N.x with hRCx
  have hRCc : RCx ≤ Subgroup.centralizer (CFSG.conjugate N.K N.x : Set G) := by
    rw [← BenderBranch.conjugate_centralizer]
    exact BenderBranch.conjugate_mono
      (fun r hr => c.SC_le_centralizer (thompsonJ_le_self _ hr)) N.x
  have hgR : ∀ r ∈ RCx, g * r = r * g := fun r hr =>
    Subgroup.mem_centralizer_iff.mp (hRCc hr) g hgKx
  have hgRN : g ∈ Subgroup.normalizer (RCx : Set G) := L257.mem_normalizer_of_commute hgR
  have hgD₀N : g ∈ Subgroup.normalizer (D₀x : Set G) :=
    BenderBranch.conjugate_eq_iff_mem_normalizer.mp hgD₀
  have hxS' : CFSG.conjugate N.S N.x = N.S := BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hxS
  have hQ₀S : D₀x ⊔ RCx ≤ N.S := by
    refine sup_le ?_ ?_
    · rw [← hxS']
      exact BenderBranch.conjugate_mono (inf_le_left.trans c.V_le_S) N.x
    · rw [← hxS']
      exact BenderBranch.conjugate_mono ((thompsonJ_le_self _).trans (L257.SC_le_S' N)) N.x
  have hgQ₀N : g ∈ Subgroup.normalizer ((D₀x ⊔ RCx : Subgroup G) : Set G) := by
    rw [← BenderBranch.conjugate_eq_iff_mem_normalizer, L257.conjugate_sup',
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgD₀N,
      BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgRN]
  have hSKQ : N.SK ≤ D₀x ⊔ RCx := c.SK_le_conjugate_sup hint
  have hKQ : N.K ⊓ (D₀x ⊔ RCx) = N.SK :=
    N.SK_sylow.eq_of_le (le_inf (L257.SK_le_K N) hSKQ) inf_le_left
      (N.tuple.sylow.isPGroup.to_le (inf_le_right.trans hQ₀S))
  have hgSK : g ∈ Subgroup.normalizer (N.SK : Set G) := by
    have h1 : CFSG.conjugate N.SK g ≤ N.K ⊓ (D₀x ⊔ RCx) := by
      refine le_inf ?_ ?_
      · rw [← BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgNK]
        exact BenderBranch.conjugate_mono (L257.SK_le_K N) g
      · rw [← BenderBranch.conjugate_eq_iff_mem_normalizer.mpr hgQ₀N]
        exact BenderBranch.conjugate_mono hSKQ g
    rw [hKQ] at h1
    exact BenderBranch.conjugate_eq_iff_mem_normalizer.mp
      (Subgroup.eq_of_le_of_card_ge h1 (by rw [BenderBranch.card_conjugate]))
  have hcommD : ∀ a ∈ D₀x, ∀ b ∈ RCx, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hRCc hb) a
      (BenderBranch.conjugate_mono (inf_le_left.trans c.V_le_K) N.x ha)
  have hSN : N.S ≤ Subgroup.normalizer (D₀x : Set G) :=
    S_le_normalizer_conjugate c.S_le_normalizer_inf
  have hcommSK : ∀ t ∈ N.SK, t⁻¹ * g⁻¹ * t * g ∈ V ⊓ V' := by
    intro t ht
    obtain ⟨d', hd', r', hr', rfl⟩ := mem_sup_of_commute hcommD (hSKQ ht)
    have hr'S : r' ∈ N.S := hQ₀S (Subgroup.mem_sup_right hr')
    have hgr : g * r' = r' * g := hgR r' hr'
    have hid : (d' * r')⁻¹ * g⁻¹ * (d' * r') * g = r'⁻¹ * (d'⁻¹ * g⁻¹ * d' * g) * r' := by
      calc (d' * r')⁻¹ * g⁻¹ * (d' * r') * g = r'⁻¹ * d'⁻¹ * g⁻¹ * d' * (r' * g) := by group
        _ = r'⁻¹ * d'⁻¹ * g⁻¹ * d' * (g * r') := by rw [hgr]
        _ = r'⁻¹ * (d'⁻¹ * g⁻¹ * d' * g) * r' := by group
    have hmemD : r'⁻¹ * (d'⁻¹ * g⁻¹ * d' * g) * r' ∈ D₀x := by
      have h1 : d'⁻¹ * g⁻¹ * d' * g ∈ D₀x := by
        have hg'd : g⁻¹ * d' * g ∈ D₀x := by
          have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (D₀x : Set G)).inv_mem
            hgD₀N) d').mp hd'
          simpa using this
        have := D₀x.mul_mem (D₀x.inv_mem hd') hg'd
        simpa [mul_assoc] using this
      have h2 := (Subgroup.mem_normalizer_iff.mp (hSN (N.S.inv_mem hr'S)) _).mp h1
      simpa [mul_assoc] using h2
    have hmemSK : (d' * r')⁻¹ * g⁻¹ * (d' * r') * g ∈ N.SK := by
      have hgi : g⁻¹ ∈ Subgroup.normalizer (N.SK : Set G) :=
        (Subgroup.normalizer (N.SK : Set G)).inv_mem hgSK
      have h1 : g⁻¹ * (d' * r') * g ∈ N.SK := by
        have := (Subgroup.mem_normalizer_iff.mp hgi (d' * r')).mp ht
        simpa using this
      have := N.SK.mul_mem (N.SK.inv_mem ht) h1
      simpa [mul_assoc] using this
    rw [hid] at hmemSK ⊢
    exact c.SK_inf_conjugate_le hint ⟨hmemSK, hmemD⟩
  have hgcent : g ∈ Subgroup.centralizer (N.K : Set G) :=
    c.autodd g hgNK hgSK hpodd hcommSK
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    rw [hk0', pow_zero, orderOf_eq_one_iff] at hk
    apply hDh
    intro d _
    rw [hk]
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simp)
  have hmdvd : p ^ (k - 1) ∣ orderOf g := by
    rw [hgord]
    exact pow_dvd_pow p (Nat.sub_le k 1)
  have hyo : orderOf (g ^ p ^ (k - 1)) = p := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hmdvd, hgord,
      Nat.pow_div (Nat.sub_le k 1) hp.pos]
    have : k - (k - 1) = 1 := by omega
    rw [this, pow_one]
  have hyN : g ^ p ^ (k - 1) ∈ Subgroup.normalizer (E : Set G) :=
    (Subgroup.normalizer (E : Set G)).pow_mem hgNE _
  have hyC : g ^ p ^ (k - 1) ∈ Subgroup.centralizer (N.K : Set G) :=
    (Subgroup.centralizer (N.K : Set G)).pow_mem hgcent _
  have hcomm : ∀ a ∈ P₀, a * g ^ p ^ (k - 1) = g ^ p ^ (k - 1) * a := fun a ha =>
    Subgroup.mem_centralizer_iff.mp hyC a (hP₀K ha)
  have hyP : g ^ p ^ (k - 1) ∉ P₀ := by
    intro hyP
    have hyZ : g ^ p ^ (k - 1) ∈ centerOf N.K := ⟨hP₀K hyP, hyC⟩
    have h2 : (g ^ p ^ (k - 1)) ^ 2 = 1 := c.center_elem.2 _ hyZ
    have hdvd : p ∣ 2 := hyo ▸ orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  exact L257.cube_contradiction he2 hcore hp hp2 hP₀ hP₀card (hP₀K.trans hKN) hyN hyo hcomm hyP

end Conf257

end CFSG.QuasithinUnique
