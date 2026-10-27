module

public import CFSG.CGT.PushingUpLit.C2L.Gomi0

public section

namespace CFSG.CGT.PushingUpLit.C2L

open CFSG CFSG.ABGLocalTools CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.T2KSW
open scoped commutatorElement

variable {G : Type} [Group G]

section Sylow

variable [Finite G]

theorem lt_inf_normalizer_of_lt {P A : Subgroup G} (hP : IsPGroup 2 P) (hAP : A < P) :
    A < P ⊓ Subgroup.normalizer (A : Set G) := by
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  have hlt : A.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, Subgroup.subgroupOf_eq_top]
    exact fun h => hAP.not_ge h
  have hn := Group.normalizerCondition_of_isNilpotent (A.subgroupOf P) hlt
  rw [← Subgroup.subgroupOf_normalizer_eq hAP.le] at hn
  obtain ⟨s, hs1, hs2⟩ := IsConcreteLE.exists_of_lt hn
  refine lt_of_le_of_ne (le_inf hAP.le Subgroup.le_normalizer) fun heq => ?_
  apply hs2
  have hs3 : (s : G) ∈ P ⊓ Subgroup.normalizer (A : Set G) := ⟨s.2, hs1⟩
  rw [← heq] at hs3
  exact hs3

theorem le_of_isSylowOf_of_normal {N S K : Subgroup G} (hS : IsSylowOf 2 S N) (hKN : K ≤ N)
    (hn : N ≤ Subgroup.normalizer (K : Set G)) (hK : IsPGroup 2 K) : K ≤ S := by
  obtain ⟨h, hh, hhK⟩ := exists_mem_conj_mem_of_isSylowOf hS hKN hK
  intro y hy
  have h1 : h * y * h⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hn hh) y).1 hy
  have h2 := hhK _ h1
  simpa [mul_assoc] using h2

theorem oTwoIn_le_of_isSylowOf {N S : Subgroup G} (hS : IsSylowOf 2 S N) : oTwoIn N ≤ S :=
  le_of_isSylowOf_of_normal hS (oTwoIn_le N) (le_normalizer_oTwoIn N) (isPGroup_oTwoIn N)

omit [Finite G] in
theorem isSylowOf_inf_of_forall {P N : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (h : ∀ P₁ : Subgroup G, IsSylowOf 2 P₁ ⊤ → P₁ ≠ P → ¬ P ⊓ N ≤ P₁) :
    IsSylowOf 2 (P ⊓ N) N := by
  have hp : IsPGroup 2 ↥(P ⊓ N : Subgroup G) := hP.isPGroup.to_inf_left
  obtain ⟨S', hS', hle⟩ := exists_isSylowOf_ge (inf_le_right : P ⊓ N ≤ N) hp
  obtain ⟨P₁, hP₁, hS'P₁⟩ := exists_isSylowOf_ge (le_top : S' ≤ ⊤) hS'.isPGroup
  have hPP₁ : P₁ = P := by
    by_contra hne
    exact h P₁ hP₁ hne (hle.trans hS'P₁)
  rw [hPP₁] at hS'P₁
  have : S' = P ⊓ N := le_antisymm (le_inf hS'P₁ hS'.le) hle
  rwa [← this]

theorem isSylowOf_inf_normalizer_of_forall {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hDP : D < P)
    (hmax : ∀ P₁ : Subgroup G, IsSylowOf 2 P₁ ⊤ → P₁ ≠ P → ¬ D < P ⊓ P₁) :
    IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G)) (Subgroup.normalizer (D : Set G)) := by
  refine isSylowOf_inf_of_forall hP fun P₁ hP₁ hne hle => hmax P₁ hP₁ hne ?_
  exact lt_of_lt_of_le (lt_inf_normalizer_of_lt hP.isPGroup hDP) (le_inf inf_le_left hle)

theorem inf_lt_left_of_ne {P Q : Subgroup G} (hP : IsSylowOf 2 P ⊤) (hQ : IsSylowOf 2 Q ⊤)
    (hne : P ≠ Q) : P ⊓ Q < P := by
  refine lt_of_le_of_ne inf_le_left fun h => hne ?_
  have hPQ : P ≤ Q := by rw [← h]; exact inf_le_right
  exact (hP.eq_of_le hPQ le_top hQ.isPGroup).symm

end Sylow

section Intersections

variable [Finite G] {H : Subgroup G}

theorem GomiH.exists_sylow_ne (h : GomiH H) (P : Subgroup G) :
    ∃ R : Subgroup G, IsSylowOf 2 R ⊤ ∧ R ≠ P ∧ H ≤ R := by
  have hnc := h.not_twoClosed
  rw [twoClosed_iff_forall_eq] at hnc
  push Not at hnc
  obtain ⟨S₁, S₂, hS₁, hS₂, hne⟩ := hnc
  obtain ⟨P₁, hP₁, hSP₁⟩ := exists_isSylowOf_ge (le_top : S₁ ≤ ⊤) hS₁.isPGroup
  obtain ⟨P₂, hP₂, hSP₂⟩ := exists_isSylowOf_ge (le_top : S₂ ≤ ⊤) hS₂.isPGroup
  have hH₁ : H ≤ S₁ := h.oTwoIn_eq ▸ oTwoIn_le_of_isSylowOf hS₁
  have hH₂ : H ≤ S₂ := h.oTwoIn_eq ▸ oTwoIn_le_of_isSylowOf hS₂
  have hP₁₂ : P₁ ≠ P₂ := by
    rintro rfl
    apply hne
    have e₁ := hS₁.eq_of_le (le_inf hSP₁ hS₁.le) inf_le_right
      (hP₁.isPGroup.to_inf_left : IsPGroup 2 ↥(P₁ ⊓ _ : Subgroup G))
    have e₂ := hS₂.eq_of_le (le_inf hSP₂ hS₂.le) inf_le_right
      (hP₁.isPGroup.to_inf_left : IsPGroup 2 ↥(P₁ ⊓ _ : Subgroup G))
    rw [← e₁, ← e₂]
  by_cases h1 : P₁ = P
  · exact ⟨P₂, hP₂, fun h2 => hP₁₂ (h1.trans h2.symm), hH₂.trans hSP₂⟩
  · exact ⟨P₁, hP₁, h1, hH₁.trans hSP₁⟩

theorem GomiD.not_lt_inf {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤) (h : GomiD P D) :
    ∀ R : Subgroup G, IsSylowOf 2 R ⊤ → R ≠ P → ¬ D < P ⊓ R := by
  intro R hR hRP hlt
  obtain ⟨R₀, ⟨hR₀, hR₀P, hDR₀⟩, hmaxR₀⟩ := Set.exists_max_image
    {R₁ : Subgroup G | IsSylowOf 2 R₁ ⊤ ∧ R₁ ≠ P ∧ D < P ⊓ R₁}
    (fun R₁ => Nat.card ↥(P ⊓ R₁)) (Set.toFinite _) ⟨R, hR, hRP, hlt⟩
  obtain ⟨A, hA⟩ : ∃ A : Subgroup G, P ⊓ R₀ = A := ⟨_, rfl⟩
  have hAP : A < P := hA ▸ inf_lt_left_of_ne hP hR₀ hR₀P.symm
  have hAR : A < R₀ := by
    rw [← hA, inf_comm]
    exact inf_lt_left_of_ne hR₀ hP hR₀P
  have hDA : D < A := hA ▸ hDR₀
  have hmaxA : ∀ R₁ : Subgroup G, IsSylowOf 2 R₁ ⊤ → R₁ ≠ P → D < P ⊓ R₁ →
      Nat.card ↥(P ⊓ R₁) ≤ Nat.card ↥A := fun R₁ h1 h2 h3 =>
    hA ▸ hmaxR₀ R₁ ⟨h1, h2, h3⟩
  have key : ∀ H' : Subgroup G, A ≤ H' → H' ≤ P →
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (H' : Set G) →
      IsSylowOf 2 (P ⊓ Subgroup.normalizer (H' : Set G)) (Subgroup.normalizer (H' : Set G)) := by
    intro H' _ _ hNH
    refine isSylowOf_inf_of_forall hP fun P₁ hP₁ hne hle => ?_
    have h1 : A < P ⊓ P₁ := lt_of_lt_of_le (lt_inf_normalizer_of_lt hP.isPGroup hAP)
      (le_inf inf_le_left ((inf_le_inf_left P hNH).trans hle))
    exact absurd (hmaxA P₁ hP₁ hne (hDA.trans h1)) (not_le.2 (Subgroup.card_lt_of_lt h1))
  have hNA : ¬ TwoClosed (Subgroup.normalizer (A : Set G)) := by
    intro hc
    have hS := key A le_rfl hAP.le le_rfl
    obtain ⟨S, hS', hle⟩ := exists_isSylowOf_ge
      (inf_le_right : R₀ ⊓ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (A : Set G))
      (hR₀.isPGroup.to_inf_left : IsPGroup 2 ↥(R₀ ⊓ Subgroup.normalizer (A : Set G) : Subgroup G))
    have heq := twoClosed_iff_forall_eq.1 hc _ _ hS' hS
    have h1 : R₀ ⊓ Subgroup.normalizer (A : Set G) ≤ A := by
      have h2 : R₀ ⊓ Subgroup.normalizer (A : Set G) ≤ P ⊓ R₀ :=
        le_inf ((hle.trans heq.le).trans inf_le_left) inf_le_left
      rwa [hA] at h2
    exact (lt_inf_normalizer_of_lt hR₀.isPGroup hAR).not_ge h1
  obtain ⟨H, ⟨hAH, hHP, hNH⟩, hmaxH⟩ := Set.exists_max_image
    {H' : Subgroup G | A ≤ H' ∧ H' ≤ P ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (H' : Set G)}
    (fun H' => Nat.card ↥H') (Set.toFinite _) ⟨A, le_rfl, hAP.le, le_rfl⟩
  have hKey := key H hAH hHP hNH
  have hOP : oTwoIn (Subgroup.normalizer (H : Set G)) ≤ P :=
    (oTwoIn_le_of_isSylowOf hKey).trans inf_le_left
  have hHO : H ≤ oTwoIn (Subgroup.normalizer (H : Set G)) :=
    le_oTwoIn_of_normal Subgroup.le_normalizer le_rfl (hP.isPGroup.to_le hHP)
  have hOH : H = oTwoIn (Subgroup.normalizer (H : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hHO (hmaxH _ ⟨hAH.trans hHO, hOP,
      hNH.trans (le_normalizer_oTwoIn _)⟩)
  have hDH : D < H := hDA.trans_le hAH
  have hGH : GomiH H := by
    refine ⟨fun hb => ?_, fun hc => hNA (hc.mono hNH), hOH.symm⟩
    exact absurd (hb ▸ hDH) not_lt_bot
  exact hDH.not_ge (h.2 ⟨hGH, hHP⟩ hDH.le)

theorem GomiD.lt {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤) (h : GomiD P D) : D < P := by
  refine lt_of_le_of_ne h.1.2 fun heq => ?_
  apply h.1.1.not_twoClosed
  rw [heq]
  exact ⟨P, hP.of_le Subgroup.le_normalizer le_top, le_rfl⟩

theorem GomiD.isSylowOf_inf_normalizer {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤)
    (h : GomiD P D) :
    IsSylowOf 2 (P ⊓ Subgroup.normalizer (D : Set G)) (Subgroup.normalizer (D : Set G)) :=
  isSylowOf_inf_normalizer_of_forall hP (h.lt hP) (h.not_lt_inf hP)

theorem exists_eq_map_conj_of_isSylowOf {N B S : Subgroup G} (hB : IsSylowOf 2 B N)
    (hS : IsSylowOf 2 S N) : ∃ n ∈ N, S = B.map (MulAut.conj n).toMonoidHom := by
  obtain ⟨n, hn, hnS⟩ := exists_mem_conj_mem_of_isSylowOf hB hS.le hS.isPGroup
  refine ⟨n, hn, ?_⟩
  have hle : S ≤ B.map (MulAut.conj n).toMonoidHom := fun y hy =>
    ⟨n⁻¹ * y * n, hnS y hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj n).injective, hB.card_eq, hS.card_eq]

theorem isSylowOf_top_map_conj {P : Subgroup G} (hP : IsSylowOf 2 P ⊤) (g : G) :
    IsSylowOf 2 (P.map (MulAut.conj g).toMonoidHom) ⊤ := by
  have := (isSylowOf_map_conj_iff (A := P) (B := ⊤) g).2 hP
  rwa [Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective] at this

theorem GomiD.inf_eq {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤) (h : GomiD P D)
    {S₁ S₂ : Subgroup G} (h₁ : IsSylowOf 2 S₁ (Subgroup.normalizer (D : Set G)))
    (h₂ : IsSylowOf 2 S₂ (Subgroup.normalizer (D : Set G))) (hne : S₁ ≠ S₂) : S₁ ⊓ S₂ = D := by
  have hB := h.isSylowOf_inf_normalizer hP
  have hDS₁ : D ≤ S₁ := h.1.1.oTwoIn_eq ▸ oTwoIn_le_of_isSylowOf h₁
  have hDS₂ : D ≤ S₂ := h.1.1.oTwoIn_eq ▸ oTwoIn_le_of_isSylowOf h₂
  refine le_antisymm ?_ (le_inf hDS₁ hDS₂)
  by_contra hnle
  have hlt : D < S₁ ⊓ S₂ := lt_of_le_not_ge (le_inf hDS₁ hDS₂) hnle
  obtain ⟨n₁, hn₁, e₁⟩ := exists_eq_map_conj_of_isSylowOf hB h₁
  obtain ⟨n₂, hn₂, e₂⟩ := exists_eq_map_conj_of_isSylowOf hB h₂
  have hN : ∀ n ∈ Subgroup.normalizer (D : Set G),
      (Subgroup.normalizer (D : Set G)).map (MulAut.conj n).toMonoidHom =
        Subgroup.normalizer (D : Set G) := fun n hn =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hn)
  have hD : ∀ n ∈ Subgroup.normalizer (D : Set G), D.map (MulAut.conj n).toMonoidHom = D :=
    fun n hn => Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
  have hS : ∀ n ∈ Subgroup.normalizer (D : Set G), (P ⊓ Subgroup.normalizer (D : Set G)).map
      (MulAut.conj n).toMonoidHom = P.map (MulAut.conj n).toMonoidHom ⊓
        Subgroup.normalizer (D : Set G) := fun n hn => by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj n).injective, hN n hn]
  rw [hS n₁ hn₁] at e₁
  rw [hS n₂ hn₂] at e₂
  have hU := (h.map_conj n₁)
  rw [hD n₁ hn₁] at hU
  have hP₁ := isSylowOf_top_map_conj hP n₁
  have hP₂ := isSylowOf_top_map_conj hP n₂
  have hle : S₁ ⊓ S₂ ≤ P.map (MulAut.conj n₁).toMonoidHom ⊓ P.map (MulAut.conj n₂).toMonoidHom :=
    le_inf_iff.2 ⟨inf_le_left.trans (e₁ ▸ inf_le_left), inf_le_right.trans (e₂ ▸ inf_le_left)⟩
  have heq : P.map (MulAut.conj n₂).toMonoidHom = P.map (MulAut.conj n₁).toMonoidHom := by
    by_contra hne'
    exact hU.not_lt_inf hP₁ _ hP₂ hne' (lt_of_lt_of_le hlt hle)
  exact hne (by rw [e₁, e₂, heq])

end Intersections

section Quotient

theorem exists_fusionStronglyEmbedded_quotient {X : Type*} [Group X] [Finite X]
    {Dn B : Subgroup X} [Dn.Normal] (hB : IsSylowOf 2 B ⊤) (hDB : Dn < B)
    (hTI : ∀ n : X, Dn < B ⊓ B.map (MulAut.conj n).toMonoidHom →
      n ∈ Subgroup.normalizer (B : Set X))
    (hnn : ¬ B.Normal) :
    ∃ K : Subgroup (X ⧸ Dn), CFSG.Open.fusionStronglyEmbedded K := by
  set π : X →* X ⧸ Dn := QuotientGroup.mk' Dn with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Dn
  have hker : π.ker = Dn := QuotientGroup.ker_mk' Dn
  have hBbar : IsSylowOf 2 (B.map π) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hB.isPGroup.map π, ?_⟩
    rw [Subgroup.relIndex_top_right]
    intro h
    have h1 := h.trans (Subgroup.index_map_dvd B hπ)
    have hB' := (isSylowOf_iff.1 hB).2.2
    rw [Subgroup.relIndex_top_right] at hB'
    exact hB' h1
  have hB1 : B.map π ≠ ⊥ := by
    intro hb
    rw [Subgroup.map_eq_bot_iff, hker] at hb
    exact hDB.not_ge hb
  have hHtop : Subgroup.normalizer ((B.map π : Subgroup (X ⧸ Dn)) : Set (X ⧸ Dn)) ≠ ⊤ := by
    intro htop
    apply hnn
    have hnorm : (B.map π).Normal := Subgroup.normalizer_eq_top_iff.1 htop
    have hcomap : B = (B.map π).comap π := by
      rw [Subgroup.comap_map_eq, hker, sup_eq_left.2 hDB.le]
    rw [hcomap]
    infer_instance
  refine ⟨Subgroup.normalizer ((B.map π : Subgroup (X ⧸ Dn)) : Set (X ⧸ Dn)),
    fusionStronglyEmbedded_of_normalizer_le hBbar hB1 hHtop fun P' hP'B hP'1 x hx => ?_⟩
  obtain ⟨n, rfl⟩ := hπ x
  obtain ⟨⟨y, hyP'⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hP'1
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hz : π n * y * (π n)⁻¹ ∈ P' := (Subgroup.mem_normalizer_iff.1 hx y).1 hyP'
  obtain ⟨b, hbB, hb⟩ := hP'B hz
  obtain ⟨b'', hb''B, hb''⟩ := hP'B hyP'
  have hDn : Dn.map (MulAut.conj n).toMonoidHom = Dn :=
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (by
      rw [Subgroup.normalizer_eq_top_iff.2 ‹Dn.Normal›]; exact Subgroup.mem_top n)
  have hd : (n * b'' * n⁻¹)⁻¹ * b ∈ Dn := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hb, hb'']
    group
  have hDnB : Dn ≤ B.map (MulAut.conj n).toMonoidHom := by
    have := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hDB.le
    rwa [hDn] at this
  have hbn : b ∈ B.map (MulAut.conj n).toMonoidHom := by
    have h1 : n * b'' * n⁻¹ ∈ B.map (MulAut.conj n).toMonoidHom :=
      ⟨b'', hb''B, by simp [MulAut.conj_apply]⟩
    have h2 := mul_mem h1 (hDnB hd)
    have e : n * b'' * n⁻¹ * ((n * b'' * n⁻¹)⁻¹ * b) = b := by group
    rwa [e] at h2
  have hbD : b ∉ Dn := by
    intro hbD
    have h1 : π b = 1 := (QuotientGroup.eq_one_iff b).2 hbD
    rw [hb] at h1
    apply hy1'
    have e : y = (π n)⁻¹ * (π n * y * (π n)⁻¹) * π n := by group
    rw [e, h1]
    group
  have hlt : Dn < B ⊓ B.map (MulAut.conj n).toMonoidHom :=
    lt_of_le_not_ge (le_inf hDB.le hDnB) fun hle => hbD (hle ⟨hbB, hbn⟩)
  exact Subgroup.le_normalizer_map π ⟨n, hTI n hlt, rfl⟩

theorem GomiD.gomiH0 [Finite G] {P D : Subgroup G} (hP : IsSylowOf 2 P ⊤) (h : GomiD P D) :
    GomiH0 D := by
  refine ⟨h.1.1, ?_⟩
  have hSyl := h.isSylowOf_inf_normalizer hP
  have hDP : D < P ⊓ Subgroup.normalizer (D : Set G) :=
    lt_inf_normalizer_of_lt hP.isPGroup (h.lt hP)
  obtain ⟨Q, hQ⟩ := hSyl.exists_sylow_eq_subgroupOf
  have hB : IsSylowOf 2 ((P ⊓ Subgroup.normalizer (D : Set G)).subgroupOf
      (Subgroup.normalizer (D : Set G))) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, hQ ▸ Q.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right, ← hQ]
    exact Q.not_dvd_index
  have hN : ∀ n ∈ Subgroup.normalizer (D : Set G),
      (Subgroup.normalizer (D : Set G)).map (MulAut.conj n).toMonoidHom =
        Subgroup.normalizer (D : Set G) := fun n hn =>
    Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hn)
  have hD : ∀ n ∈ Subgroup.normalizer (D : Set G), D.map (MulAut.conj n).toMonoidHom = D :=
    fun n hn => Subgroup.mem_normalizer_iff_map_conj_eq.1 hn
  refine exists_fusionStronglyEmbedded_quotient hB ?_ ?_ ?_
  · obtain ⟨x, hxB, hxD⟩ := IsConcreteLE.exists_of_lt hDP
    refine lt_of_le_of_ne (fun y hy => ?_) fun heq => hxD ?_
    · rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact ⟨h.1.2 hy, y.2⟩
    · have hx : (⟨x, hxB.2⟩ : Subgroup.normalizer (D : Set G)) ∈
          (P ⊓ Subgroup.normalizer (D : Set G)).subgroupOf (Subgroup.normalizer (D : Set G)) :=
        Subgroup.mem_subgroupOf.2 hxB
      rw [← heq] at hx
      exact Subgroup.mem_subgroupOf.1 hx
  · intro n hn
    obtain ⟨y, hyI, hyD⟩ := IsConcreteLE.exists_of_lt hn
    obtain ⟨hy1, b, hb, hby⟩ := Subgroup.mem_inf.1 hyI
    have hyP : (y : G) ∈ P := (Subgroup.mem_subgroupOf.1 hy1).1
    have hbP : (b : G) ∈ P := (Subgroup.mem_subgroupOf.1 hb).1
    have hyPn : (y : G) ∈ P.map (MulAut.conj (n : G)).toMonoidHom :=
      ⟨b, hbP, by rw [← hby]; simp [MulAut.conj_apply]⟩
    have hyD' : (y : G) ∉ D := fun hyD' => hyD (Subgroup.mem_subgroupOf.2 hyD')
    have hDn : D ≤ P.map (MulAut.conj (n : G)).toMonoidHom := by
      have := Subgroup.map_mono (f := (MulAut.conj (n : G)).toMonoidHom) h.1.2
      rwa [hD n n.2] at this
    have hDlt : D < P ⊓ P.map (MulAut.conj (n : G)).toMonoidHom :=
      lt_of_le_not_ge (le_inf h.1.2 hDn) fun hle => hyD' (hle ⟨hyP, hyPn⟩)
    have hPn : P.map (MulAut.conj (n : G)).toMonoidHom = P := by
      by_contra hne
      exact h.not_lt_inf hP _ (isSylowOf_top_map_conj hP _) hne hDlt
    have hPN : (P ⊓ Subgroup.normalizer (D : Set G)).map (MulAut.conj (n : G)).toMonoidHom =
        P ⊓ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.map_inf _ _ _ (MulAut.conj (n : G)).injective, hPn, hN n n.2]
    have hnPN : (n : G) ∈ Subgroup.normalizer ((P ⊓ Subgroup.normalizer (D : Set G) :
        Subgroup G) : Set G) := Subgroup.mem_normalizer_iff_map_conj_eq.2 hPN
    have : n ∈ (Subgroup.normalizer ((P ⊓ Subgroup.normalizer (D : Set G) : Subgroup G) :
        Set G)).subgroupOf (Subgroup.normalizer (D : Set G)) := Subgroup.mem_subgroupOf.2 hnPN
    rwa [Subgroup.subgroupOf_normalizer_eq inf_le_right] at this
  · intro hnorm
    exact h.1.1.not_twoClosed ⟨_, hSyl,
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).1 hnorm⟩

end Quotient

section Transport

theorem fusionStronglyEmbedded_map_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {K : Subgroup X} (hK : CFSG.Open.fusionStronglyEmbedded K) :
    CFSG.Open.fusionStronglyEmbedded (K.map e.toMonoidHom) := by
  obtain ⟨hKtop, hKeven, hK⟩ := hK
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    apply hKtop
    have h1 : (K.map e.toMonoidHom).comap e.toMonoidHom = ⊤ := by
      rw [htop]
      exact Subgroup.comap_top _
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h1
  · rwa [Subgroup.card_map_of_injective e.injective]
  · intro g hg
    obtain ⟨x, rfl⟩ := e.surjective g
    have hx : x ∉ K := fun hx => hg ⟨x, hx, rfl⟩
    have h1 := hK x hx
    have e1 : (K.map e.toMonoidHom).map (MulAut.conj (e x)⁻¹).toMonoidHom =
        (K.map (MulAut.conj x⁻¹).toMonoidHom).map e.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext y
      simp
    rw [e1, ← Subgroup.map_inf _ _ _ e.injective, Subgroup.card_map_of_injective e.injective]
    exact h1

theorem exists_fusionStronglyEmbedded_quot_congr {X Y : Type*} [Group X] [Group Y]
    (f : X ≃* Y) {Dn : Subgroup X} {Dn' : Subgroup Y} [Dn.Normal] [Dn'.Normal]
    (h : Dn.map f.toMonoidHom = Dn') :
    (∃ K : Subgroup (X ⧸ Dn), CFSG.Open.fusionStronglyEmbedded K) →
      ∃ K : Subgroup (Y ⧸ Dn'), CFSG.Open.fusionStronglyEmbedded K := by
  rintro ⟨K, hK⟩
  exact ⟨K.map (QuotientGroup.congr Dn Dn' f h).toMonoidHom,
    fusionStronglyEmbedded_map_mulEquiv _ hK⟩

theorem StronglyEmbeddedMod.map_conj {H : Subgroup G} (h : StronglyEmbeddedMod H) (g : G) :
    StronglyEmbeddedMod (H.map (MulAut.conj g).toMonoidHom) := by
  have hN : (Subgroup.normalizer (H : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
    Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)
  let ψ : ↥(Subgroup.normalizer (H : Set G)) ≃*
      ↥(Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hN)
  refine exists_fusionStronglyEmbedded_quot_congr ψ ?_ h
  ext y'
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : G), Subgroup.mem_subgroupOf.1 hy, rfl⟩
  · intro hy'
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_subgroupOf.1 hy'
    refine ⟨⟨x, Subgroup.le_normalizer hx⟩, Subgroup.mem_subgroupOf.2 hx, ?_⟩
    exact Subtype.ext hxy

theorem GomiH0.map_conj [Finite G] {H : Subgroup G} (h : GomiH0 H) (g : G) :
    GomiH0 (H.map (MulAut.conj g).toMonoidHom) :=
  ⟨h.1.map_conj g, h.2.map_conj g⟩

end Transport

end CFSG.CGT.PushingUpLit.C2L
