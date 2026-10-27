module

public import CFSG.GH74.GLS.C3.Layer1.St1MProps

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools
open scoped commutatorElement

section M0

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_of_commutator_le {M M₀ : Subgroup G} (hc : ⁅M, M⁆ ≤ M₀) {m h : G} (hm : m ∈ M)
    (hh : h ∈ M) (hh₀ : h ∈ M₀) : m * h * m⁻¹ ∈ M₀ := by
  have h1 : ⁅m, h⁆ ∈ M₀ := hc (Subgroup.commutator_mem_commutator hm hh)
  have h2 : m * h * m⁻¹ = ⁅m, h⁆ * h := by
    simp only [commutatorElement_def]; group
  rw [h2]
  exact M₀.mul_mem h1 hh₀

theorem exists_M0 {M : Subgroup G} {t : G} (hnot : t ∉ ⁅M, M⁆) :
    ∃ M₀ : Subgroup G, ⁅M, M⁆ ≤ M₀ ∧ M₀ ≤ M ∧ t ∉ M₀ ∧
      ∀ H : Subgroup G, M₀ < H → H ≤ M → t ∈ H := by
  have hD : ⁅M, M⁆ ≤ M := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  obtain ⟨M₀, ⟨hDM₀, hM₀M, htM₀⟩, hmax⟩ := Set.Finite.exists_maximal
    (s := {H : Subgroup G | ⁅M, M⁆ ≤ H ∧ H ≤ M ∧ t ∉ H}) (Set.toFinite _)
    ⟨⁅M, M⁆, le_rfl, hD, hnot⟩
  refine ⟨M₀, hDM₀, hM₀M, htM₀, fun H hlt hHM => ?_⟩
  by_contra htH
  exact hlt.ne (le_antisymm hlt.le (hmax ⟨hDM₀.trans hlt.le, hHM, htH⟩ hlt.le))

omit [Finite G] in
theorem exists_subgroup_union {M M₀ : Subgroup G} (hc : ⁅M, M⁆ ≤ M₀) (hM₀M : M₀ ≤ M) {u : G}
    (huM : u ∈ M) (hu2 : u * u ∈ M₀) :
    ∃ H : Subgroup G, M₀ ≤ H ∧ H ≤ M ∧ u ∈ H ∧ ∀ x ∈ H, x ∈ M₀ ∨ u⁻¹ * x ∈ M₀ := by
  have hinvu : u⁻¹ ∈ M := M.inv_mem huM
  have hconj : ∀ h ∈ M₀, u⁻¹ * h * u ∈ M₀ := fun h hh => by
    have := conj_mem_of_commutator_le hc hinvu (hM₀M hh) hh
    simpa using this
  let H : Subgroup G :=
    { carrier := {x | x ∈ M₀ ∨ u⁻¹ * x ∈ M₀}
      one_mem' := Or.inl M₀.one_mem
      mul_mem' := by
        intro x y hx hy
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact Or.inl (M₀.mul_mem hx hy)
        · right
          have h1 : u⁻¹ * (x * y) = (u⁻¹ * x * u) * (u⁻¹ * y) := by group
          rw [h1]
          exact M₀.mul_mem (hconj x hx) hy
        · right
          have h1 : u⁻¹ * (x * y) = (u⁻¹ * x) * y := by group
          rw [h1]
          exact M₀.mul_mem hx hy
        · left
          have h2 : x * y = (u * u) * (u⁻¹ * (u⁻¹ * x) * u) * (u⁻¹ * y) := by group
          rw [h2]
          exact M₀.mul_mem (M₀.mul_mem hu2 (hconj _ hx)) hy
      inv_mem' := by
        intro x hx
        rcases hx with hx | hx
        · exact Or.inl (M₀.inv_mem hx)
        · right
          have h1 : u⁻¹ * x⁻¹ = (u⁻¹ * (u⁻¹ * x)⁻¹ * u) * (u * u)⁻¹ := by group
          rw [h1]
          exact M₀.mul_mem (hconj _ (M₀.inv_mem hx)) (M₀.inv_mem hu2) }
  refine ⟨H, fun x hx => Or.inl hx, fun x hx => ?_, Or.inr (by simp), fun x hx => hx⟩
  rcases hx with hx | hx
  · exact hM₀M hx
  · have : x = u * (u⁻¹ * x) := by group
    rw [this]
    exact M.mul_mem huM (hM₀M hx)

omit [Finite G] in
theorem involution_mod_M0 {M M₀ : Subgroup G} {t u : G} (hc : ⁅M, M⁆ ≤ M₀) (hM₀M : M₀ ≤ M)
    (htM₀ : t ∉ M₀) (hmax : ∀ H : Subgroup G, M₀ < H → H ≤ M → t ∈ H) (huM : u ∈ M)
    (huM₀ : u ∉ M₀) (hu2 : u * u ∈ M₀) : t⁻¹ * u ∈ M₀ := by
  obtain ⟨H, hM₀H, hHM, huH, hH⟩ := exists_subgroup_union hc hM₀M huM hu2
  have hlt : M₀ < H := lt_of_le_of_ne hM₀H fun h => huM₀ (h ▸ huH)
  rcases hH t (hmax H hlt hHM) with h | h
  · exact absurd h htM₀
  · have := M₀.inv_mem h
    simpa using this

theorem exists_two_involutions {R : Type} [Group R] [Finite R] {H : Subgroup R}
    (h : 1 < CFSG.Open.pRank 2 H) :
    ∃ a ∈ H, ∃ b ∈ H, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧ a * a = 1 ∧ b * b = 1 := by
  obtain ⟨E, hEH, hE, hcard⟩ := CFSG.GH74.Uniqueness.SU.SU1.exists_pRank (p := 2) one_lt_two H
  have h4 : 4 ≤ Nat.card E := by
    rw [hcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ CFSG.Open.pRank 2 H := Nat.pow_le_pow_right (by norm_num) h
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  have hne : E ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at h4
    omega
  obtain ⟨a', ha'⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have haE : (a' : R) ∈ E := a'.2
  have ha1 : (a' : R) ≠ 1 := fun e => ha' (Subtype.ext e)
  have hnle : ¬ E ≤ Subgroup.zpowers (a' : R) := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hsq _ haE) ha1] at h1
    omega
  obtain ⟨b, hbE, hbz⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
  have hb1 : b ≠ 1 := fun e => hbz (by rw [e]; exact Subgroup.one_mem _)
  have hab : (a' : R) ≠ b := fun e => hbz (by rw [← e]; exact Subgroup.mem_zpowers _)
  exact ⟨a', hEH haE, b, hEH hbE, ha1, hb1, hab, hsq _ haE, hsq _ hbE⟩

theorem exists_cyclic_gen {M M₀ S : Subgroup G} {t : G} (hc : ⁅M, M⁆ ≤ M₀) (hM₀M : M₀ ≤ M)
    (htM₀ : t ∉ M₀) (hmax : ∀ H : Subgroup G, M₀ < H → H ≤ M → t ∈ H) (hSM : S ≤ M)
    (hS : IsPGroup 2 ↥S) :
    ∃ b ∈ S, ∀ s ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * s ∈ S ⊓ M₀ := by
  set N : Subgroup ↥S := (S ⊓ M₀).subgroupOf S with hN
  have hmemN : ∀ x : ↥S, x ∈ N ↔ (x : G) ∈ M₀ := fun x => by
    rw [hN, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hNn : N.Normal := ⟨fun n hn s => by
    rw [hmemN] at hn ⊢
    exact conj_mem_of_commutator_le hc (hSM s.2) (hSM n.2) hn⟩
  have hRp : IsPGroup 2 (↥S ⧸ N) := hS.to_quotient N
  have hcomm : ∀ a b : ↥S ⧸ N, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hmemN]
        have : ((x * y)⁻¹ * (y * x) : ↥S) = ⟨⁅(y : G)⁻¹, (x : G)⁻¹⁆, by
            rw [commutatorElement_def, inv_inv, inv_inv]
            exact S.mul_mem (S.mul_mem (S.mul_mem (S.inv_mem y.2) (S.inv_mem x.2)) y.2) x.2⟩ := by
          apply Subtype.ext
          simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
          group
        rw [this]
        exact hc (Subgroup.commutator_mem_commutator (M.inv_mem (hSM y.2)) (M.inv_mem (hSM x.2)))
  have huniq : ∀ a b : ↥S ⧸ N, a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a = b := by
    intro a b ha hb ha1 hb1
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        have hx2 : (x : G) * x ∈ M₀ := by
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemN] at ha
          exact ha
        have hy2 : (y : G) * y ∈ M₀ := by
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hmemN] at hb
          exact hb
        have hx0 : (x : G) ∉ M₀ := fun h => ha1 ((QuotientGroup.eq_one_iff x).mpr ((hmemN x).mpr h))
        have hy0 : (y : G) ∉ M₀ := fun h => hb1 ((QuotientGroup.eq_one_iff y).mpr ((hmemN y).mpr h))
        have h1 := involution_mod_M0 hc hM₀M htM₀ hmax (hSM x.2) hx0 hx2
        have h2 := involution_mod_M0 hc hM₀M htM₀ hmax (hSM y.2) hy0 hy2
        rw [QuotientGroup.eq, hmemN]
        have := M₀.mul_mem (M₀.inv_mem h1) h2
        simpa [mul_assoc] using this
  have hrank : ¬ 1 < CFSG.Open.pRank 2 (⊤ : Subgroup (↥S ⧸ N)) := by
    intro h
    obtain ⟨a, -, b, -, ha1, hb1, hab, ha2, hb2⟩ := exists_two_involutions h
    exact hab (huniq a b ha2 hb2 ha1 hb1)
  have hcyc : IsCyclic (↥S ⧸ N) := by
    have hP : IsPGroup 2 ↥(⊤ : Subgroup (↥S ⧸ N)) :=
      hRp.of_equiv Subgroup.topEquiv.symm
    have := CFSG.ComponentClassification.AschbacherTheorem5.SevenFour.isCyclic_of_commute_of_pRank_le_one
      (P := (⊤ : Subgroup (↥S ⧸ N))) hP (not_lt.mp hrank) (fun a _ b _ => hcomm a b)
    exact isCyclic_of_surjective (⊤ : Subgroup (↥S ⧸ N)).subtype Subgroup.topEquiv.surjective
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨(b : G), b.2, fun s hs => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg (QuotientGroup.mk ⟨s, hs⟩))
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  have := (hmemN _).mp hk
  refine ⟨k, Subgroup.mem_inf.mpr ⟨S.mul_mem (S.inv_mem (S.zpow_mem b.2 k)) hs, ?_⟩⟩
  simpa using this

end M0

section Transfer

variable {G : Type} [Group G] [Finite G]

open CFSG.GH74.GLS.Bg.Thompson

theorem exists_transfer_conj (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {M M₀ S : Subgroup G} {t : G} (hSG : IsSylowOf 2 S ⊤) (hc : ⁅M, M⁆ ≤ M₀) (hM₀M : M₀ ≤ M)
    (htM₀ : t ∉ M₀) (hmax : ∀ H : Subgroup G, M₀ < H → H ≤ M → t ∈ H) (hSM : S ≤ M)
    (htS : t ∈ S) (ht2 : orderOf t = 2) :
    ∃ g : G, g⁻¹ * t * g ∈ S ⊓ M₀ ∧ ∀ c ∈ S ⊓ centralizer ({t} : Set G), g⁻¹ * c * g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSle, hSp, hSdvd⟩ := isSylowOf_iff.mp hSG
  have hSdvd' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSdvd
  have hQn : ∀ s ∈ S, ∀ q ∈ S ⊓ M₀, s * q * s⁻¹ ∈ S ⊓ M₀ := fun s hs q hq =>
    ⟨S.mul_mem (S.mul_mem hs hq.1) (S.inv_mem hs),
      conj_mem_of_commutator_le hc (hSM hs) (hSM hq.1) hq.2⟩
  have ht1 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
  obtain ⟨b, hbS, hb⟩ := exists_cyclic_gen hc hM₀M htM₀ hmax hSM hSp
  have key := thompson_transfer_1515 (p := 2) (X := G) (P := S) (Q := S ⊓ M₀) (u := t) hSp hSdvd'
    hQn ⟨b, hbS, hb⟩ htS (fun h => htM₀ h.2)
    (fun g k _ => by
      have : t ^ (2 * k) = 1 := by rw [pow_mul, ht1, one_pow]
      rw [this]
      simp)
    (fun g hgS _ => by
      have hgsq : (g⁻¹ * t * g) * (g⁻¹ * t * g) = 1 := by
        have : (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
        rw [this, show t * t = 1 by rw [← sq]; exact ht1]
        group
      by_cases hmem : g⁻¹ * t * g ∈ M₀
      · exact Or.inl ⟨hgS, hmem⟩
      · right
        have := involution_mod_M0 hc hM₀M htM₀ hmax (hSM hgS) hmem (by rw [hgsq]; exact M₀.one_mem)
        exact ⟨S.mul_mem (S.inv_mem htS) hgS, this⟩)
  rcases key with ⟨N, hN, hcyc, -, htN⟩ | ⟨g, hgQ, -, hgC⟩
  · exfalso
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    ·
      subst h
      have hcycG : IsCyclic G := by
        have := hcyc
        exact isCyclic_of_surjective (QuotientGroup.quotientBot (G := G)).toMonoidHom
          (QuotientGroup.quotientBot (G := G)).surjective
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (mul_comm' a b)
    · exact htN (h ▸ Subgroup.mem_top t)
  · exact ⟨g, hgQ, fun c hc' => (hgC c hc').1⟩

end Transfer

section Core

variable {G : Type} [Group G] [Finite G]

open CFSG.RankTwoShapes CFSG.GH74.GLS.Stage1.Thm3.Sec4

theorem alperin_mem {S A M : Subgroup G} (hA : IsEStar A) (h6A1 : gammaK 2 S (pRank 2 G) ≤ M)
    {c : G} (h : AlperinDecomposition 2 S A c) : c ∈ M := by
  induction h with
  | one => exact M.one_mem
  | @step c n Q hcd hQ hAQ hn ih =>
      refine M.mul_mem ih ?_
      have hEs : IsEStar (cmap c⁻¹ A) := isEStar_cmap hA c⁻¹
      have hrank : pRank 2 G ≤ pRank 2 ↥Q := le_pRank_of_elem hAQ hEs.1 (k := pRank 2 G) hEs.2
      exact h6A1 ((le_iSup₂_of_le Q hQ.1 (le_iSup_of_le hrank le_rfl) :
        normalizer (Q : Set G) ≤ gammaK 2 S (pRank 2 G)) hn)

theorem prop810a_core (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) {M S : Subgroup G}
    (hSG : IsSylowOf 2 S ⊤) (hSM : S ≤ M) (h6A1 : gammaK 2 S (pRank 2 G) ≤ M) {t : G}
    (htS : t ∈ S) (ht2 : orderOf t = 2) (hrk : pRank 2 ↥(S ⊓ centralizer ({t} : Set G)) = pRank 2 G) :
    t ∈ ⁅M, M⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hnot
  obtain ⟨M₀, hc, hM₀M, htM₀, hmax⟩ := exists_M0 hnot
  obtain ⟨g, hgQ, hgC⟩ := exists_transfer_conj hG hnab hSG hc hM₀M htM₀ hmax hSM htS ht2
  obtain ⟨A, hAT, hA⟩ := exists_isEStar_le hrk
  have hAS : A ≤ S := hAT.trans inf_le_left
  have htA : t ∈ A := hA.mem_of_commute ht2 fun a ha =>
    (mem_centralizer_singleton_iff.mp (hAT ha).2).symm
  have hAg : cmap g⁻¹ A ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    have := hgC a ⟨hAS ha, (hAT ha).2⟩
    simpa [MulAut.conj_apply] using this
  obtain ⟨hSle, hSp, hSdvd⟩ := isSylowOf_iff.mp hSG
  have hSdvd' : ¬ 2 ∣ S.index := by rwa [Subgroup.relIndex_top_right] at hSdvd
  set S' : Sylow 2 G := hSp.toSylow hSdvd' with hS'
  have hSsub : (S' : Subgroup G) = S := IsPGroup.toSylow_coe hSp hSdvd'
  obtain ⟨c, hcd, hceq⟩ := alperin_centric_radical_fusion S' (P := A) (hSsub ▸ hAS)
    (g := g) (hSsub ▸ hAg)
  rw [hSsub] at hcd
  have hcM : c ∈ M := alperin_mem hA h6A1 hcd
  have e : c⁻¹ * t * c = g⁻¹ * t * g := hceq t htA
  have hcomm : t⁻¹ * c⁻¹ * t * c ∈ M₀ := by
    apply hc
    have := Subgroup.commutator_mem_commutator (M.inv_mem (hSM htS)) (M.inv_mem hcM)
    simpa [commutatorElement_def] using this
  have : t = (g⁻¹ * t * g) * (t⁻¹ * c⁻¹ * t * c)⁻¹ := by rw [← e]; group
  exact htM₀ (by rw [this]; exact M₀.mul_mem hgQ.2 (M₀.inv_mem hcomm))

end Core

section Final

variable {G : Type} [Group G] [Finite G]

open CFSG.GH74.GLS.Stage1.Thm3.Sec4

theorem gammaK_cmap_le {S M : Subgroup G} {k : ℕ} {m : G} (hm : m ∈ M) (h : gammaK 2 S k ≤ M) :
    gammaK 2 (cmap m S) k ≤ M := by
  refine iSup₂_le fun Q hQS => iSup_le fun hk => ?_
  intro g hg
  set Q' := cmap m⁻¹ Q with hQ'
  have hQ'S : Q' ≤ S := by
    have h1 : cmap m⁻¹ Q ≤ cmap m⁻¹ (cmap m S) := Subgroup.map_mono hQS
    rwa [cmap_inv_cancel] at h1
  have hrank : k ≤ pRank 2 ↥Q' := by rw [hQ', pRank_cmap]; exact hk
  have hQQ' : Q = cmap m Q' := (cmap_cancel m Q).symm
  have hg' : m⁻¹ * g * m ∈ normalizer (Q' : Set G) := by
    have h2 := (mem_normalizer_cmap_iff (c := m) (y := m⁻¹ * g * m) (K := Q')).mp
    rw [← hQQ'] at h2
    apply h2
    rw [show m * (m⁻¹ * g * m) * m⁻¹ = g by group]
    exact hg
  have hmem : m⁻¹ * g * m ∈ M :=
    h ((le_iSup₂_of_le Q' hQ'S (le_iSup_of_le hrank le_rfl) :
      normalizer (Q' : Set G) ≤ gammaK 2 S k) hg')
  have e : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
  rw [e]
  exact M.mul_mem (M.mul_mem hm hmem) (M.inv_mem hm)

theorem exists_conj_le_of_isSylowOf {M S T : Subgroup G} (hS : IsSylowOf 2 S M) (hTM : T ≤ M)
    (hT : IsPGroup 2 ↥T) : ∃ m ∈ M, T ≤ cmap m S := by
  obtain ⟨Q, hQ⟩ := hS.exists_sylow_eq_subgroupOf
  have hTp : IsPGroup 2 ↥(T.subgroupOf M) := hT.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow_two hTp Q
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  rw [mem_cmap]
  have h1 := hg ⟨x, hTM hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
  rw [hQ] at h1
  have h2 := Subgroup.mem_subgroupOf.mp h1
  simpa using h2

theorem prop810a
    (hG : C3Hyp G) (T4 : St1Thm4 G) {A M S : Subgroup G} (hA : IsEStar A)
    (hMN : normalizer (thetaGA A : Set G) ≤ M) (hS : IsSylowOf 2 S M) (hAS : A ≤ S) :
    ∀ t ∈ M, orderOf t = 2 → pRank 2 ↥(centralizer ({t} : Set G) ⊓ M) = pRank 2 ↥M →
      t ∈ ⁅M, M⁆ := by
  intro t htM ht2 hrk
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hr : pRank 2 G = 4 := hG.pRank_eq_four
  have hSp : IsPGroup 2 ↥S := hS.isPGroup
  have hSG : IsSylowOf 2 S ⊤ := isSylowOf_top_of_theta hr T4 hS hA hAS hMN
  have h6A1 := gammaK_S_le_of_theta hr T4 hSp hA hAS hMN
  have hMr : pRank 2 ↥M = 4 := by
    refine le_antisymm (hr ▸ Bg.pRank_subgroup_le one_lt_two M) ?_
    exact le_pRank_of_elem (hAS.trans hS.le) hA.1 (k := 4) (by rw [hA.2, hr])
  have htC : t ∈ centralizer ({t} : Set G) ⊓ M := ⟨mem_centralizer_singleton_iff.mpr rfl, htM⟩
  have htp : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨T, hT, hzT⟩ := exists_isSylowOf_ge (N := centralizer ({t} : Set G) ⊓ M) (K := zpowers t)
    (zpowers_le.mpr htC) htp
  have htT : t ∈ T := hzT (mem_zpowers t)
  obtain ⟨m, hmM, hTm⟩ := exists_conj_le_of_isSylowOf hS (hT.le.trans inf_le_right) hT.isPGroup
  have hMc : cmap m M = M := cmap_eq_of_mem_normalizer (Subgroup.le_normalizer hmM)
  have hTc : cmap m (⊤ : Subgroup G) = ⊤ :=
    cmap_eq_of_mem_normalizer (Subgroup.le_normalizer (Subgroup.mem_top m))
  have hS₁M : IsSylowOf 2 (cmap m S) M := by
    have := isSylowOf_cmap hS m
    rwa [hMc] at this
  have hS₁G : IsSylowOf 2 (cmap m S) ⊤ := by
    have := isSylowOf_cmap hSG m
    rwa [hTc] at this
  have hrk' : pRank 2 ↥(cmap m S ⊓ centralizer ({t} : Set G)) = pRank 2 G := by
    refine le_antisymm (Bg.pRank_subgroup_le one_lt_two _) ?_
    have hle : T ≤ cmap m S ⊓ centralizer ({t} : Set G) := le_inf hTm (hT.le.trans inf_le_left)
    have h1 := Bg.pRank_subgroup_mono one_lt_two hle
    rw [pRank_eq_of_isSylowOf hT, hrk, hMr] at h1
    omega
  exact prop810a_core hG.kproper.1 hG.kproper.2.1 hS₁G hS₁M.le (gammaK_cmap_le hmM h6A1)
    (hTm htT) ht2 hrk'

theorem b_iv2_8_10a
    : B_iv2_8_10a := fun _ _ _ hG T4 _ _ _ hA _ _ hMN hS hAS =>
  prop810a hG T4 hA hMN hS hAS

end Final

end CFSG.GH74.GLS
