module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSwapN9XN
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Lemma44

public section

namespace CFSG.ComponentClassification.SolMax.SwapP2

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

private theorem prod_mem_of_diag_conj {G : Type*} [Group G] {Q : Subgroup G} [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) {P : Subgroup (G × G)} {g : G} (hgQ : g ∈ Q) (hg1 : g ≠ 1)
    (hdiag : ∀ a ∈ Q, (a, a) ∈ P) (hconj : ∀ a ∈ Q, (g * a * g⁻¹, a) ∈ P) :
    ∀ a ∈ Q, ∀ b ∈ Q, (a, b) ∈ P := by
  let P₁ : Subgroup G := P.comap (MonoidHom.inl G G)
  have hmem : ∀ c : G, c ∈ P₁ ↔ (c, (1 : G)) ∈ P := fun c => Iff.rfl
  have hnorm : ∀ a ∈ Q, ∀ c ∈ P₁, a * c * a⁻¹ ∈ P₁ := by
    intro a ha c hc
    rw [hmem] at hc ⊢
    have h1 : (a * c * a⁻¹, (1 : G)) = (a, a) * (c, 1) * (a, a)⁻¹ := by simp
    rw [h1]
    exact mul_mem (mul_mem (hdiag a ha) hc) (inv_mem (hdiag a ha))
  have hKn : (P₁.subgroupOf Q).Normal := ⟨fun k hk q => by
    show ((q * k * q⁻¹ : Q) : G) ∈ P₁
    exact hnorm q q.2 k hk⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P₁.subgroupOf Q) with hbot | htop
  · exfalso
    have hcen : (⟨g, hgQ⟩ : Q) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro a
      have h1 : ((a : G)⁻¹ * g * (a : G) * g⁻¹, (1 : G)) ∈ P := by
        have h2 : ((a : G)⁻¹ * g * (a : G) * g⁻¹, (1 : G)) =
            ((a : G), (a : G))⁻¹ * (g * (a : G) * g⁻¹, (a : G)) := by
          simp [mul_assoc]
        rw [h2]
        exact mul_mem (inv_mem (hdiag a a.2)) (hconj a a.2)
      have h3 : (a⁻¹ * ⟨g, hgQ⟩ * a * ⟨g, hgQ⟩⁻¹ : Q) ∈ P₁.subgroupOf Q := h1
      rw [hbot, Subgroup.mem_bot] at h3
      have h4 : a⁻¹ * ⟨g, hgQ⟩ * a = ⟨g, hgQ⟩ := mul_inv_eq_one.mp h3
      have h5 : (⟨g, hgQ⟩ : Q) * a = a * ⟨g, hgQ⟩ := by
        calc (⟨g, hgQ⟩ : Q) * a = a * (a⁻¹ * ⟨g, hgQ⟩ * a) := by group
          _ = a * ⟨g, hgQ⟩ := by rw [h4]
      exact h5.symm
    have hZ : Subgroup.center Q = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
      · exact h
      · exfalso
        obtain ⟨a, b, hab⟩ := hnc
        have ha : a ∈ Subgroup.center Q := by rw [h]; exact Subgroup.mem_top a
        exact hab (Subgroup.mem_center_iff.mp ha b).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hg1 (congrArg Subtype.val hcen)
  · have hone : ∀ c ∈ Q, (c, (1 : G)) ∈ P := fun c hc => by
      have : (⟨c, hc⟩ : Q) ∈ P₁.subgroupOf Q := by rw [htop]; exact Subgroup.mem_top _
      exact this
    intro a ha b hb
    have h2 : ((1 : G), b) ∈ P := by
      have h3 := mul_mem (hdiag b hb) (hone b⁻¹ (inv_mem hb))
      simpa using h3
    have h4 := mul_mem (hone a ha) h2
    simpa using h4

private theorem odd_dvd_card_zstar_aux {Q : Type} [Group Q] [Finite Q] {d : ℕ} (hd : Odd d)
    (h : d ∣ Nat.card (Q ⧸ pPrimeCore 2 Q)) : d ∣ Nat.card (Q ⧸ Open.fusionZStar Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 (center (Q ⧸ pPrimeCore 2 Q)) :=
    GrSLit.GrS4.isPGroup_center_quotient Q
  have hcop : Nat.Coprime d (Nat.card (center (Q ⧸ pPrimeCore 2 Q))) := by
    refine Nat.coprime_of_dvd fun p hp hpd hpZ => ?_
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hpZ
    obtain ⟨k, hk⟩ := hZ z
    have h2 : p ∣ 2 ^ k := by
      rw [← hz]
      exact orderOf_dvd_of_pow_eq_one hk
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    subst hp2
    exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hpd)
  have hfus : Open.fusionZStar Q =
      (center (Q ⧸ pPrimeCore 2 Q)).comap (QuotientGroup.mk' (pPrimeCore 2 Q)) :=
    GrSLit.GrS4.fusionZStar_eq_comap_pPrimeCore Q
  have hidx : (Open.fusionZStar Q).index = (center (Q ⧸ pPrimeCore 2 Q)).index := by
    rw [hfus]
    exact Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hcard : (center (Q ⧸ pPrimeCore 2 Q)).index *
      Nat.card (center (Q ⧸ pPrimeCore 2 Q)) = Nat.card (Q ⧸ pPrimeCore 2 Q) :=
    Subgroup.index_mul_card _
  rw [← hcard] at h
  have h' : d ∣ (center (Q ⧸ pPrimeCore 2 Q)).index := hcop.dvd_of_dvd_mul_right h
  rw [← hidx] at h'
  exact h'

private theorem card_mul_self_dvd_quotient {S G A : Type*} [Group S] [Group G] [Group A]
    {K : Subgroup G} [K.Normal] (ε : S →* G ⧸ K) (Ψ : S →* A × A) (hker : ε.ker ≤ Ψ.ker)
    {Q : Subgroup A} (hle : Q.prod Q ≤ Ψ.range) :
    Nat.card Q * Nat.card Q ∣ Nat.card (G ⧸ K) := by
  have hindex : Ψ.ker.index ∣ ε.ker.index := Subgroup.index_dvd_of_le hker
  rw [Subgroup.index_ker, Subgroup.index_ker] at hindex
  have h1 := Subgroup.card_dvd_of_le hle
  rw [Nat.card_congr (Subgroup.prodEquiv Q Q).toEquiv, Nat.card_prod] at h1
  exact h1.trans (hindex.trans (Subgroup.card_subgroup_dvd_card _))

section Exact

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  {M F : Subgroup X} {DF : Finset (Fin n)} {f : X} {L N : Subgroup X}

theorem ExactData.dvd_card (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) : 3600 ∣ Nat.card (↥N ⧸ pPrimeCore 2 ↥N) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨θ⟩ := hs.alt
  obtain ⟨ρ, hρ⟩ := exists_isPermAction (M := M) (by omega) (by omega) θ
  have hfN := ExactRho.f_mem_normalizer hs hx
  have hLN := ExactRho.L_le_normalizer hs hx
  have h4 := ExactRho.card_support_rho hs hx hρ
  have hρcongr : ∀ (a b : X) (ha : a ∈ normalizer (M : Set X)) (hb : b ∈ normalizer (M : Set X)),
      a = b → ρ ⟨a, ha⟩ = ρ ⟨b, hb⟩ := fun a b ha hb h => by subst h; rfl
  have hL₁data := SwapN9.fixedLayer_data hs.le hs.pc hρ hfN (ExactRho.f_mul_self hx) h4.le
    (by omega) (N := GSLit.fixedLayer M (zpowers f)) rfl
  have hL₁C : GSLit.fixedLayer M (zpowers f) ≤ Hn E ⊓ centralizer ({f} : Set X) := hL₁data.1
  have hL₁pc : IsPComponent 2 ((GSLit.fixedLayer M (zpowers f)).subgroupOf
      (Hn E ⊓ centralizer ({f} : Set X))) := hL₁data.2.1
  set σ := ρ ⟨f, hfN⟩
  have h5 : 5 ≤ n - σ.support.card := by omega
  have hQsimple := ExactRho.isSimpleGroup_altFixPerm h5
  have hQnc := ExactRho.exists_not_comm_altFixPerm h5
  have hQcard : Nat.card (ExactRho.altFixPerm σ) = 60 := by
    have h2 : 2 ≤ n - σ.support.card := by omega
    rw [ExactRho.card_altFixPerm h2, h4, show n - 4 = 5 by omega] <;> norm_num [Nat.factorial]
  have hLQ : ∀ (z : X) (hz : z ∈ L), ρ ⟨z, hLN hz⟩ ∈ ExactRho.altFixPerm σ := fun z hz =>
    ExactRho.rho_mem_altFixPerm hs hx hρ hz
  have hQL : ∀ g ∈ ExactRho.altFixPerm σ, ∃ (z : X) (hz : z ∈ L), ρ ⟨z, hLN hz⟩ = g :=
    fun g hg => ExactRho.exists_rho_eq hs hn hx hρ hg
  obtain ⟨y, hyL₁, hyO⟩ : ∃ y ∈ GSLit.fixedLayer M (zpowers f), y ∉ core M := by
    by_contra hall
    have h1 : GSLit.fixedLayer M (zpowers f) ≤ (pPrimeCore 2 ↥M).map M.subtype := fun y hy =>
      Classical.byContradiction fun hy' => hall ⟨y, hy, hy'⟩
    have h2 := card_dvd_of_le h1
    rw [card_map_of_injective M.subtype_injective] at h2
    have h3 := two_dvd_card_of_isPComponent_in hL₁C hL₁pc
    have h4' := Nat.Coprime.coprime_dvd_right h2 pPrimeCore_coprime_card
    exact absurd h4' (by
      rw [Nat.coprime_two_left]
      exact Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr h3))
  have hyM : y ∈ M := (mem_inf.mp (GSLit.fixedLayer_le_inf M (zpowers f) hyL₁)).1
  have hyN : y ∈ normalizer (M : Set X) := le_normalizer hyM
  have hNy : conjBy N y = N := hx.conj_eq hs hn hyL₁ hyO
  obtain ⟨g, hg⟩ : ∃ g : Perm (Fin n), ρ ⟨y, hyN⟩ = g := ⟨_, rfl⟩
  have hgQ : g ∈ ExactRho.altFixPerm σ :=
    hg ▸ ExactRho.rho_mem_altFixPerm_of_mem_fixedLayer hs hn hx hρ hyL₁ hyN
  have hg1 : g ≠ 1 := by
    intro h1
    apply hyO
    refine mem_core_of_mem_coreActionKernel hρ (by omega) hyM (hρ.mem_coreActionKernel hyN ?_)
    rw [hg, h1]
  obtain ⟨hMtH, hMtpc⟩ := isPComponent_conj hs.le hs.pc
    (hs.cent (mem_centralizer_singleton_iff.mpr rfl))
  have hMtK : conjBy M t ≤ UnbalancedLayer.coreActionKernel M :=
    GSThmB.B5a.le_coreActionKernel_of_ne hs.le hMtH hs.pc hMtpc (Ne.symm hs.swap)
  have hcyM : t * y * t⁻¹ ∈ conjBy M t := ⟨y, hyM, rfl⟩
  have hcyK : t * y * t⁻¹ ∈ UnbalancedLayer.coreActionKernel M := hMtK hcyM
  have hcyN : t * y * t⁻¹ ∈ normalizer (M : Set X) := hcyK.1
  have hcy1 : ρ ⟨t * y * t⁻¹, hcyN⟩ = 1 := hρ.eq_one_of_mem_coreActionKernel (by omega) hcyK
  have hcL : ∀ l ∈ L, t * l * t⁻¹ = l := by
    intro l hl
    have hlt : t * l = l * t :=
      (mem_centralizer_singleton_iff.mp (hs.sig.pair.1.2.1 (hx.LJ hl))).symm
    rw [hlt]
    group
  let c : X →* X := (MulAut.conj t).toMonoidHom
  let T : Subgroup X := normalizer (M : Set X) ⊓ (normalizer (M : Set X)).comap c
  let S : Subgroup X := N ⊓ T
  have hSN : S ≤ N := inf_le_left
  have hSNm : S ≤ normalizer (M : Set X) := fun s hs' => (mem_inf.mp (mem_inf.mp hs').2).1
  have hSc : ∀ s ∈ S, c s ∈ normalizer (M : Set X) := fun s hs' =>
    (mem_inf.mp (mem_inf.mp hs').2).2
  let i₁ : ↥S →* ↥(normalizer (M : Set X)) := Subgroup.inclusion hSNm
  let i₂ : ↥S →* ↥(normalizer (M : Set X)) :=
    (c.comp S.subtype).codRestrict _ fun s => hSc s s.2
  let Ψ : ↥S →* Perm (Fin n) × Perm (Fin n) := (ρ.comp i₁).prod (ρ.comp i₂)
  have hΨ : ∀ (s : X) (hsS : s ∈ S),
      Ψ ⟨s, hsS⟩ = (ρ ⟨s, hSNm hsS⟩, ρ ⟨c s, hSc s hsS⟩) := fun s hsS => rfl
  let ε : ↥S →* ↥N ⧸ pPrimeCore 2 ↥N :=
    (QuotientGroup.mk' (pPrimeCore 2 ↥N)).comp (Subgroup.inclusion hSN)
  have hker : ε.ker ≤ Ψ.ker := by
    rintro ⟨s, hsS⟩ hs'
    have hs'' : ((⟨s, hSN hsS⟩ : ↥N) : ↥N ⧸ pPrimeCore 2 ↥N) = 1 := hs'
    have h1 : (⟨s, hSN hsS⟩ : ↥N) ∈ pPrimeCore 2 ↥N := (QuotientGroup.eq_one_iff _).mp hs''
    have h2 : s ∈ (pPrimeCore 2 ↥N).map N.subtype := ⟨_, h1, rfl⟩
    have h3 : s ∈ core (centralizer ({f} : Set X)) :=
      pPrimeCore_le_of_isPComponent hx.NC hx.Npc h2
    have h6 : t * s * t⁻¹ ∈ core (centralizer ({f} : Set X)) :=
      (mem_normalizer_iff.mp (Sol78.le_normalizer_map_subtype
        (pPrimeCore 2 ↥(centralizer ({f} : Set X))) (hx.t_mem_centralizer hs)) s).mp h3
    rw [MonoidHom.mem_ker, hΨ]
    exact Prod.ext (ExactRho.rho_eq_one_of_mem_core hs hn hx hρ h3 (hSNm hsS))
      (ExactRho.rho_eq_one_of_mem_core hs hn hx hρ h6 (hSc s hsS))
  have hlS : ∀ l ∈ L, l ∈ S := fun l hl =>
    ⟨hx.LN hl, hLN hl, show t * l * t⁻¹ ∈ normalizer (M : Set X) by rw [hcL l hl]; exact hLN hl⟩
  have hdiag : ∀ a ∈ ExactRho.altFixPerm σ, (a, a) ∈ Ψ.range := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := hQL a ha
    refine ⟨⟨l, hlS l hl⟩, ?_⟩
    rw [hΨ]
    exact Prod.ext rfl (hρcongr _ _ _ _ (hcL l hl))
  have hconj : ∀ a ∈ ExactRho.altFixPerm σ, (g * a * g⁻¹, a) ∈ Ψ.range := by
    intro a ha
    obtain ⟨l, hl, rfl⟩ := hQL a ha
    have hid : t * (y * l * y⁻¹) * t⁻¹ = (t * y * t⁻¹) * l * (t * y * t⁻¹)⁻¹ := by
      calc t * (y * l * y⁻¹) * t⁻¹ = (t * y * t⁻¹) * (t * l * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
        _ = (t * y * t⁻¹) * l * (t * y * t⁻¹)⁻¹ := by rw [hcL l hl]
    have hylN : y * l * y⁻¹ ∈ normalizer (M : Set X) :=
      mul_mem (mul_mem hyN (hLN hl)) (inv_mem hyN)
    have hylS : y * l * y⁻¹ ∈ S := by
      have h1' : y * l * y⁻¹ ∈ conjBy N y := ⟨l, hx.LN hl, rfl⟩
      have hylc : t * (y * l * y⁻¹) * t⁻¹ ∈ normalizer (M : Set X) := by
        rw [hid]
        exact mul_mem (mul_mem hcyN (hLN hl)) (inv_mem hcyN)
      exact ⟨hNy.le h1', hylN, hylc⟩
    refine ⟨⟨y * l * y⁻¹, hylS⟩, ?_⟩
    rw [hΨ]
    refine Prod.ext ?_ ?_
    · show ρ ⟨y * l * y⁻¹, hSNm hylS⟩ = g * ρ ⟨l, hLN hl⟩ * g⁻¹
      have : (⟨y * l * y⁻¹, hSNm hylS⟩ : ↥(normalizer (M : Set X))) =
          ⟨y, hyN⟩ * ⟨l, hLN hl⟩ * ⟨y, hyN⟩⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hg]
    · show ρ ⟨t * (y * l * y⁻¹) * t⁻¹, hSc _ hylS⟩ = ρ ⟨l, hLN hl⟩
      have : (⟨t * (y * l * y⁻¹) * t⁻¹, hSc _ hylS⟩ : ↥(normalizer (M : Set X))) =
          ⟨t * y * t⁻¹, hcyN⟩ * ⟨l, hLN hl⟩ * ⟨t * y * t⁻¹, hcyN⟩⁻¹ := Subtype.ext hid
      rw [this, map_mul, map_mul, map_inv, hcy1]
      simp
  have hQQ := prod_mem_of_diag_conj hQnc hgQ hg1 hdiag hconj
  have hle : (ExactRho.altFixPerm σ).prod (ExactRho.altFixPerm σ) ≤ Ψ.range := fun p hp => by
    obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
    simpa using hQQ p.1 hp1 p.2 hp2
  have h1 := card_mul_self_dvd_quotient ε Ψ hker hle
  rw [hQcard] at h1
  simpa using h1

theorem ExactData.dvd_card_zstar (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) : 225 ∣ Nat.card (↥N ⧸ Open.fusionZStar ↥N) :=
  odd_dvd_card_zstar_aux ⟨112, by norm_num⟩ ((by norm_num : 225 ∣ 3600).trans (hx.dvd_card hs hn))

theorem ExactData.false_of_alt (hs : Setting t J n e E D M) (hn : n = 9)
    (hx : ExactData t J n e F DF f L N) {m : ℕ} (hmo : Odd m) (hm7 : 7 ≤ m)
    (θ : ↥N ⧸ pPrimeCore 2 ↥N ≃* alternatingGroup (Fin m)) : False := by
  have hmn : m ≤ n := hs.sig.pair.2.2.2.1 f N m ⟨hx.orderOf_f, hx.NC, hx.Npc, ⟨θ⟩⟩ hmo
  have hd := hx.dvd_card hs hn
  rw [Nat.card_congr θ.toEquiv] at hd
  exact not_dvd_alt_three_six_hundred m hmo hm7 (by omega) hd

end Exact

end CFSG.ComponentClassification.SolMax.SwapP2
