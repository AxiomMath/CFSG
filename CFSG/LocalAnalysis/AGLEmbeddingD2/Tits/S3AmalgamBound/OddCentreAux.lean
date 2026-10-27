module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OddCentreTransfer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open
open scoped commutatorElement

theorem card_eq_card_map_mul {Y : Type*} [Group Y] (P N : Subgroup Y) [N.Normal] (hNP : N ≤ P) :
    Nat.card P = Nat.card (P.map (QuotientGroup.mk' N)) * Nat.card N := by
  set f : ↥P →* Y ⧸ N := (QuotientGroup.mk' N).comp P.subtype with hf
  have hker : f.ker = N.subgroupOf P := by
    ext x
    simp [hf, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : f.range = P.map (QuotientGroup.mk' N) := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card P = Nat.card (↥P ⧸ f.ker) * Nat.card f.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have h2 : Nat.card (↥P ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.ker = Nat.card N := by
    rw [hker]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNP).toEquiv
  rw [h1, h2, h3, hrange]


theorem sylow_facts {Y : Type} [Group Y] [Finite Y]
    (hZ3 : Nat.card (Subgroup.center Y) = 3)
    (hS : (Nat.card (Y ⧸ Subgroup.center Y)).factorization 3 = 2) (P₁ : Sylow 3 Y) :
    Subgroup.center Y ≤ (P₁ : Subgroup Y) ∧ Nat.card (P₁ : Subgroup Y) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZp : IsPGroup 3 (Subgroup.center Y) := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [hZ3]; simp⟩
  refine ⟨IsPGroup.le_sylow_of_normal hZp P₁, ?_⟩
  rw [Sylow.card_eq_multiplicity P₁]
  have hcard : Nat.card Y = Nat.card (Y ⧸ Subgroup.center Y) * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y), hZ3]
  rw [hcard, Nat.factorization_mul (Nat.card_pos).ne' (by norm_num), Finsupp.add_apply, hS,
    Nat.Prime.factorization Nat.prime_three]
  simp

theorem orderOf_eq_three_of_mem_center {Y : Type} [Group Y] [Finite Y]
    (hZ3 : Nat.card (Subgroup.center Y) = 3) {z : Y} (hz : z ∈ Subgroup.center Y) (hz1 : z ≠ 1) :
    orderOf z = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center Y) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  exact orderOf_eq_prime h3 hz1

theorem center_le_of_elemAbelian {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ3 : Nat.card (Subgroup.center Y) = 3)
    (hS : (Nat.card (Y ⧸ Subgroup.center Y)).factorization 3 = 2)
    {E : Subgroup Y} (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) :
    Subgroup.center Y ≤ E := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := by
    rw [IsPGroup.iff_card]; exact ⟨2, by rw [hE9]; norm_num⟩
  obtain ⟨P₁, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨hZP, hP27⟩ := sylow_facts hZ3 hS P₁
  by_contra hnot
  have ⟨z, hz, hzE⟩ : ∃ z ∈ Subgroup.center Y, z ∉ E := by
    by_contra h; push Not at h; exact hnot h
  have hz1 : z ≠ 1 := fun h => hzE (h ▸ E.one_mem)
  have hzo := orderOf_eq_three_of_mem_center hZ3 hz hz1
  set Q : Subgroup Y := E ⊔ Subgroup.center Y with hQ
  have hQP : Q ≤ (P₁ : Subgroup Y) := sup_le hEP hZP
  have hEQ : E < Q := lt_of_le_of_ne le_sup_left (fun h => hzE (h ▸ Subgroup.mem_sup_right hz))
  have hcardQ : Nat.card Q = 27 := by
    have h1 : Nat.card Q ∣ 27 := hP27 ▸ Subgroup.card_dvd_of_le hQP
    have h3 : 9 < Nat.card Q := by
      by_contra hle
      push Not at hle
      have : E = Q := Subgroup.eq_of_le_of_card_ge hEQ.le (by rw [hE9]; exact hle)
      exact hEQ.ne this
    obtain ⟨k, hk, hkq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (show Nat.card Q ∣ 3 ^ 3 by simpa using h1)
    interval_cases k <;> simp_all
  have hQeq : Q = (P₁ : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge hQP (by rw [hP27, hcardQ])
  have hcomm : ∀ a ∈ (P₁ : Subgroup Y), ∀ b ∈ (P₁ : Subgroup Y), a * b = b * a := by
    intro a ha b hb
    rw [← hQeq] at ha hb
    obtain ⟨e, he, z', hz', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha
    obtain ⟨e', he', z'', hz'', rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hb
    have h1 : e * e' = e' * e := by
      have := hE.1.is_comm.comm (⟨e, he⟩ : E) ⟨e', he'⟩
      exact congrArg Subtype.val this
    have h2 : z' * z'' = z'' * z' := Subgroup.mem_center_iff.mp hz'' z'
    have h3 : z' * e' = e' * z' := (Subgroup.mem_center_iff.mp hz' e').symm
    have h4 : z'' * e = e * z'' := (Subgroup.mem_center_iff.mp hz'' e).symm
    calc e * z' * (e' * z'') = e * (z' * e') * z'' := by group
      _ = e * (e' * z') * z'' := by rw [h3]
      _ = (e * e') * (z' * z'') := by group
      _ = (e' * e) * (z'' * z') := by rw [h1, h2]
      _ = e' * (e * z'') * z' := by group
      _ = e' * (z'' * e) * z' := by rw [h4]
      _ = e' * z'' * (e * z') := by group
  have hidx : ¬ 3 ∣ (P₁ : Subgroup Y).index := Sylow.not_dvd_index P₁
  have hmem := central_mem_commutator_of_perfect (P₁ : Subgroup Y) hz (hZP hz) hzo hidx
  haveI : IsMulCommutative ↥(P₁ : Subgroup Y) :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  rw [commutator_eq_bot, Subgroup.mem_bot] at hmem
  exact hz1 (congrArg Subtype.val hmem)


theorem pow_three_mul_of_central {Y : Type*} [Group Y] {x y u : Y} (hu : ∀ g : Y, u * g = g * u)
    (hyx : y * x = u * (x * y)) : (x * y) ^ 3 = u ^ 3 * (x ^ 3 * y ^ 3) := by
  have cl : ∀ g w : Y, g * (u * w) = u * (g * w) := fun g w => by
    rw [← mul_assoc, ← hu g, mul_assoc]
  have hyx' : ∀ w : Y, y * (x * w) = u * (x * (y * w)) := fun w => by
    rw [← mul_assoc, hyx, mul_assoc, mul_assoc]
  calc (x * y) ^ 3 = x * (y * (x * (y * (x * y)))) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = x * (u * (x * (y * (y * (x * y))))) := by rw [hyx' (y * (x * y))]
    _ = u * (x * (x * (y * (y * (x * y))))) := by rw [cl x]
    _ = u * (x * (x * (y * (u * (x * (y * y)))))) := by rw [hyx' y]
    _ = u * (x * (x * (u * (y * (x * (y * y)))))) := by rw [cl y]
    _ = u * (x * (x * (u * (u * (x * (y * (y * y))))))) := by rw [hyx' (y * y)]
    _ = u * (x * (u * (x * (u * (x * (y * (y * y))))))) := by rw [cl x]
    _ = u * (u * (x * (x * (u * (x * (y * (y * y))))))) := by rw [cl x]
    _ = u * (u * (x * (u * (x * (x * (y * (y * y))))))) := by rw [cl x]
    _ = u * (u * (u * (x * (x * (x * (y * (y * y))))))) := by rw [cl x]
    _ = u ^ 3 * (x ^ 3 * y ^ 3) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]


theorem no_order_nine {Y : Type} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hZ3 : Nat.card (Subgroup.center Y) = 3)
    (hS : (Nat.card (Y ⧸ Subgroup.center Y)).factorization 3 = 2)
    (hel : ∀ Pb : Subgroup (Y ⧸ Subgroup.center Y), IsPGroup 3 Pb → Nat.card Pb = 9 →
      IsElemAbelian 3 Pb)
    (hg : ∀ Pb : Subgroup (Y ⧸ Subgroup.center Y), IsPGroup 3 Pb → Nat.card Pb = 9 →
      ∃ g ∈ Subgroup.normalizer (Pb : Set (Y ⧸ Subgroup.center Y)),
        ∀ x ∈ Pb, x ≠ 1 → g * x * g⁻¹ ∉ Subgroup.zpowers x)
    (y : Y) : orderOf y ≠ 9 := by
  classical
  intro hy9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.center Y with hZdef
  set π : Y →* Y ⧸ Z := QuotientGroup.mk' Z with hπ
  have hyp : IsPGroup 3 (Subgroup.zpowers y) := by
    rw [IsPGroup.iff_card, Nat.card_zpowers, hy9]; exact ⟨2, by norm_num⟩
  obtain ⟨P₁, hyP⟩ := hyp.exists_le_sylow
  obtain ⟨hZP, hP27⟩ := sylow_facts hZ3 hS P₁
  set P : Subgroup Y := (P₁ : Subgroup Y) with hPdef
  have hyP' : y ∈ P := hyP (Subgroup.mem_zpowers y)
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set Pb : Subgroup (Y ⧸ Z) := P.map π with hPb
  have hPb9 : Nat.card Pb = 9 := by
    have h := card_eq_card_map_mul P Z hZP
    have h' : Nat.card ↥P = Nat.card Pb * Nat.card Z := h
    rw [hP27, hZ3] at h'
    omega
  have hPbp : IsPGroup 3 Pb := P₁.isPGroup'.map π
  have hel' := hel Pb hPbp hPb9
  obtain ⟨g, hgN, hgx⟩ := hg Pb hPbp hPb9
  have hcube : ∀ x ∈ P, x ^ 3 ∈ Z := by
    intro x hx
    have : (π x) ^ 3 = 1 := hel'.2 (π x) (Subgroup.mem_map_of_mem π hx)
    rw [← map_pow] at this
    rw [← hker]; exact this
  have hcommZ : ∀ a ∈ P, ∀ b ∈ P, ⁅a, b⁆ ∈ Z := by
    intro a ha b hb
    have := hel'.1.is_comm.comm (⟨π a, Subgroup.mem_map_of_mem π ha⟩ : Pb)
      ⟨π b, Subgroup.mem_map_of_mem π hb⟩
    have h2 : π a * π b = π b * π a := congrArg Subtype.val this
    rw [← hker, MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr h2
  have hZc : ∀ z ∈ Z, ∀ g : Y, z * g = g * z := fun z hz g => (Subgroup.mem_center_iff.mp hz g).symm
  have hZ3pow : ∀ z ∈ Z, z ^ 3 = 1 := by
    intro z hz
    have := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    exact congrArg Subtype.val this
  have hcubemul : ∀ a ∈ P, ∀ b ∈ P, (a * b) ^ 3 = a ^ 3 * b ^ 3 := by
    intro a ha b hb
    set u : Y := ⁅b, a⁆ with hu
    have huZ : u ∈ Z := hcommZ b hb a ha
    have hyx : b * a = u * (a * b) := by rw [hu, commutatorElement_def]; group
    rw [pow_three_mul_of_central (hZc u huZ) hyx, hZ3pow u huZ, one_mul]
  let c : ↥P →* ↥Z :=
    { toFun := fun x => ⟨(x : Y) ^ 3, hcube x x.2⟩
      map_one' := by apply Subtype.ext; show ((1 : ↥P) : Y) ^ 3 = 1; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact hcubemul a a.2 b b.2 }
  have hcardP : Nat.card ↥P = Nat.card c.ker * Nat.card c.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup c.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange c).toEquiv, mul_comm]
  have hrange : Nat.card c.range ≤ 3 := by
    have h1 : Nat.card c.range ∣ Nat.card ↥Z := Subgroup.card_subgroup_dvd_card c.range
    rw [hZ3] at h1
    exact Nat.le_of_dvd (by norm_num) h1
  have hy3 : y ^ 3 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hy9] at this
    omega
  have hycker : (⟨y, hyP'⟩ : ↥P) ∉ c.ker := by
    intro h
    have h1 : c ⟨y, hyP'⟩ = 1 := h
    exact hy3 (congrArg Subtype.val h1)
  have hkcard : Nat.card c.ker = 9 := by
    have h1 : Nat.card c.ker ∣ 27 := hP27 ▸ (hcardP ▸ Dvd.intro _ rfl)
    have h2 : 9 ≤ Nat.card c.ker := by
      rw [hP27] at hcardP
      by_contra hlt
      push Not at hlt
      have : Nat.card c.ker * Nat.card c.range ≤ 8 * 3 :=
        Nat.mul_le_mul (by omega) hrange
      omega
    have h3 : Nat.card c.ker ≠ 27 := by
      intro h
      have : c.ker = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h, hP27])
      exact hycker (this ▸ Subgroup.mem_top _)
    have hle : Nat.card c.ker ≤ 27 := Nat.le_of_dvd (by norm_num) h1
    have key : ∀ n ≤ 27, 9 ≤ n → n ∣ 27 → n ≠ 27 → n = 9 := by decide
    exact key _ hle h2 h1 h3
  set K : Subgroup Y := c.ker.map P.subtype with hK
  have hKmem : ∀ x : Y, x ∈ K ↔ x ∈ P ∧ x ^ 3 = 1 := by
    intro x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, congrArg Subtype.val (MonoidHom.mem_ker.mp hw)⟩
    · rintro ⟨hxP, hx3⟩
      exact ⟨⟨x, hxP⟩, MonoidHom.mem_ker.mpr (Subtype.ext hx3), rfl⟩
  have hZK : Z ≤ K := fun z hz => (hKmem z).mpr ⟨hZP hz, hZ3pow z hz⟩
  have hKcard : Nat.card K = 9 := by
    rw [hK, Subgroup.card_map_of_injective P.subtype_injective]; exact hkcard
  have hKb : Nat.card (K.map π) = 3 := by
    have h := card_eq_card_map_mul K Z hZK
    have h' : Nat.card K = Nat.card (K.map π) * Nat.card Z := h
    rw [hKcard, hZ3] at h'
    omega
  obtain ⟨x₀, hx₀K, hx₀1⟩ : ∃ x₀ ∈ K, π x₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    have : K.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact (Subgroup.mem_bot).mpr (hall x hx)
    rw [this] at hKb
    simp at hKb
  have hx₀P : x₀ ∈ P := ((hKmem x₀).mp hx₀K).1
  have hx₀3 : x₀ ^ 3 = 1 := ((hKmem x₀).mp hx₀K).2
  have hπx₀ : (π x₀) ^ 3 = 1 := by rw [← map_pow, hx₀3, map_one]
  have hπx₀o : orderOf (π x₀) = 3 := orderOf_eq_prime hπx₀ hx₀1
  have hKbz : K.map π = Subgroup.zpowers (π x₀) := by
    symm
    apply Subgroup.eq_of_le_of_card_ge
    · exact (Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem π hx₀K)
    · rw [hKb, Nat.card_zpowers, hπx₀o]
  obtain ⟨gh, hgh⟩ := QuotientGroup.mk'_surjective Z g
  have hg' : π gh = g := hgh
  have hPcomap : Subgroup.comap π Pb = P :=
    Subgroup.comap_map_eq_self (by rw [hker]; exact hZP)
  have hconjP : gh * x₀ * gh⁻¹ ∈ P := by
    rw [← hPcomap, Subgroup.mem_comap, map_mul, map_mul, map_inv, hg']
    exact (Subgroup.mem_normalizer_iff.mp hgN (π x₀)).mp (Subgroup.mem_map_of_mem π hx₀P)
  have hconjK : gh * x₀ * gh⁻¹ ∈ K := (hKmem _).mpr ⟨hconjP, by rw [conj_pow, hx₀3]; simp⟩
  have hmem : g * π x₀ * g⁻¹ ∈ Subgroup.zpowers (π x₀) := by
    rw [← hKbz]
    have := Subgroup.mem_map_of_mem π hconjK
    simpa [map_mul, map_inv, hg'] using this
  exact hgx (π x₀) (Subgroup.mem_map_of_mem π hx₀P) hx₀1 hmem

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
