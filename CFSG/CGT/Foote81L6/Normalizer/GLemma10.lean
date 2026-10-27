module

public import CFSG.CGT.Foote81L6.Normalizer.GPbar
public import CFSG.CGT.Foote81L6.Normalizer.GLemma1
public import CFSG.CGT.Foote81L6.Normalizer.GAzero
public import CFSG.CGT.Foote81L6.Lemma6Key
public import CFSG.CGT.Foote81L6.Normalizer.GTvHyp
public import CFSG.CGT.Foote81L6.Normalizer.OddCentralizerCard

public section

namespace CFSG.CGT.Foote81L6.Normalizer

open Subgroup CFSG.Quasithin
open scoped IsMulCommutative

section Inputs

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ}

@[expose] def SylZInput (D : FooteCore G T m n) : Prop :=
  ∃ P : Sylow 2 ↥(centralizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G)),
    (P : Subgroup _) =
      D.T₁.subgroupOf (centralizer ((D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) : Subgroup G) : Set G))

@[expose] def Lemma4Input (D : FooteCore G T m n) : Prop :=
  ∀ g : G, g * D.a * g⁻¹ ∈ T → g * D.a * g⁻¹ ∉ D.T₁ →
    ∃ y : G, y * D.a * y⁻¹ ∈ D.T₁ ∧ y * D.a * y⁻¹ ∉ D.A ∧ y * D.a * y⁻¹ ∉ D.Astar

@[expose] def Lemma5Input (T : Subgroup G) : Prop :=
  ∀ E : Subgroup G, IsE64 T E → ∀ g : G, E.map (MulAut.conj g).toMonoidHom ≤ T →
    ∃ h ∈ T, E.map (MulAut.conj g).toMonoidHom = E.map (MulAut.conj h).toMonoidHom

end Inputs

private theorem mem_of_pow_mem_of_coprime {G : Type*} [Group G] {S : Subgroup G} {y : G} {m k : ℕ}
    (hm : y ^ m ∈ S) (hk : y ^ k ∈ S) (hcop : Nat.Coprime m k) : y ∈ S := by
  have h := Nat.gcd_eq_gcd_ab m k
  rw [hcop.gcd_eq_one, Nat.cast_one] at h
  have e : y = (y ^ m) ^ (Nat.gcdA m k) * (y ^ k) ^ (Nat.gcdB m k) := by
    rw [← zpow_natCast y m, ← zpow_natCast y k, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h, zpow_one]
  rw [e]
  exact mul_mem (zpow_mem hm _) (zpow_mem hk _)

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

theorem normalizes_commZ (hHig : HigmanHyp) (hSylN : SylNInput (T : Subgroup G))
    (hTv : TvInput D) (hquot : QuotInput (T : Subgroup G)) (hswap : SwapInput D) {p : G}
    (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x)
    (hcomm : ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁))
    (hmove : ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), p * z * p⁻¹ ≠ z)
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) {g : G} (hg : g ∈ normalizer (F : Set G)) :
    ∀ z ∈ commZ D p, g * z * g⁻¹ ∈ commZ D p := by
  haveI : IsMulCommutative ↥F :=
    ⟨⟨fun u v => Subtype.ext (TStruct.comm_of_mul_self hF.mul_self u.2 v.2)⟩⟩
  haveI := hF.finite
  obtain ⟨Q, hQ⟩ := hSylN F hF
  obtain ⟨d₀, hd₀R, -, hd₀F, -, -⟩ := D.exists_d₀ hF
  obtain ⟨d₁, hd₁R, -, hd₁F, -, -⟩ := D.exists_d₁ hF
  have h := tvHyp D hF hTv hquot hswap hQ hd₀R hd₀F hd₁R hd₁F
  obtain ⟨htv₀, hd₀1⟩ := isTransvectionWith_d₀ D hF hd₀R hd₀F
  obtain ⟨htv₁, hd₁1⟩ := isTransvectionWith_d₁ D hF hd₁R hd₁F
  have hb : (⟨D.b₀, D.b₀_mem_E64 hF⟩ : ↥F) ≠ ⟨D.b₁, D.b₁_mem_E64 hF⟩ := by
    intro h'
    have hb' : D.b₀ = D.b₁ := congrArg Subtype.val h'
    have : D.b₀ ∈ D.B₀ ⊓ D.B₁ := mem_inf.2 ⟨D.b₀_mem, hb' ▸ D.b₁_mem⟩
    rw [D.B₀_inf_B₁, mem_bot] at this
    exact D.b₀_ne_one this
  have hL1 := card_oddCentralizer_eq h.sq_eq_one h.injective htv₀ hd₀1 htv₁ hd₁1 hb
    h.dihedral_facts.1 (card_fix_d₀_d₁ D hF hd₀R hd₀F hd₁R hd₁F).le
  set pN : ↥(normalizer (F : Set G)) := ⟨p, mem_normalizer_of_comm D hF hcomm⟩ with hpN
  have hP3 : Nat.card (zpowers (NBar.π F pN)) = 3 := by
    rw [Nat.card_zpowers, orderOf_pbar D hF hcomm hcube hmove]
  have hc₀ := pbar_comm D hF hcomm ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀R⟩
    (D.B₀B₁_le_T₁ (mem_sup_left (mem_inf.1 hd₀R).1))
  have hc₁ := pbar_comm D hF hcomm ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁R⟩
    (D.B₀B₁_le_T₁ (mem_sup_right (mem_inf.1 hd₁R).1))
  have hP₀ : ∀ q ∈ zpowers (NBar.π F pN), q * NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀R⟩ =
      NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀R⟩ * q := by
    intro q hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact (Commute.zpow_left hc₀ j).eq
  have hP₁ : ∀ q ∈ zpowers (NBar.π F pN), q * NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁R⟩ =
      NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁R⟩ * q := by
    intro q hq
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact (Commute.zpow_left hc₁ j).eq
  obtain ⟨-, hinv⟩ := TvHyp.lemma10 h hHig hL1 hP3 hP₀ hP₁
  have hPmap : (zpowers (NBar.π F pN)).map (NBar.ρ F) = zpowers (NBar.ρ F (NBar.π F pN)) :=
    MonoidHom.map_zpowers _ _
  intro z hz
  have hzF : z ∈ F := Z_le_E64 D hF (commZ_le_Z D hcomm hz)
  have hzU := (mem_commV_iff D hF hcomm hcube ⟨z, hzF⟩).2 hz
  rw [← hPmap] at hzU
  have h2 := hinv (NBar.π F ⟨g, hg⟩) _ hzU
  rw [hPmap] at h2
  have h3 := (mem_commV_iff D hF hcomm hcube _).1 h2
  rwa [NBar.ρ_π] at h3

theorem le_normalizer_commZ (hHig : HigmanHyp) (hSylN : SylNInput (T : Subgroup G))
    (hTv : TvInput D) (hquot : QuotInput (T : Subgroup G)) (hswap : SwapInput D) {p : G}
    (hcube : ∀ x ∈ D.T₁, p ^ 3 * x * (p ^ 3)⁻¹ = x)
    (hcomm : ∀ x ∈ D.T₁, p * x * p⁻¹ * x⁻¹ ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁))
    (hmove : ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), p * z * p⁻¹ ≠ z)
    {E : Subgroup G} (hE : IsE64 (T : Subgroup G) E) :
    (T : Subgroup G) ≤ normalizer ((commZ D p : Subgroup G) : Set G) := by
  have hnorm : ∀ {F : Subgroup G}, IsE64 (T : Subgroup G) F → ∀ g ∈ normalizer (F : Set G),
      g ∈ normalizer ((commZ D p : Subgroup G) : Set G) := fun hF g hg =>
    TStruct.mem_normalizer_of_forall_conj_mem
      (normalizes_commZ D hHig hSylN hTv hquot hswap hcube hcomm hmove hF hg)
  obtain ⟨-, -, hW, -⟩ := D.E64_decomp hE
  obtain ⟨Es, hEs, hsN⟩ := exists_E64_s D hW
  obtain ⟨Et, hEt, htN⟩ := exists_E64_t D hW
  have hs := hnorm hEs D.s hsN
  have ht := hnorm hEt D.t htN
  have hT₁ : D.T₁ ≤ normalizer ((commZ D p : Subgroup G) : Set G) := fun y hy =>
    TStruct.mem_normalizer_of_forall_conj_mem fun z hz => by
      rw [comm_of_mem_T₁_of_mem_Z D hy (commZ_le_Z D hcomm hz), mul_inv_cancel_right]
      exact hz
  intro x hx
  rcases D.mem_T_iff.1 hx with h0 | h0
  · rcases D.mem_T₁_or_mul_s_mem_T₁ h0 with h1 | h1
    · exact hT₁ h1
    · rw [show x = (x * D.s) * D.s⁻¹ by group]
      exact mul_mem (hT₁ h1) (inv_mem hs)
  · rcases D.mem_T₁_or_mul_s_mem_T₁ h0 with h1 | h1
    · rw [show x = (x * D.t) * D.t⁻¹ by group]
      exact mul_mem (hT₁ h1) (inv_mem ht)
    · rw [show x = (x * D.t * D.s) * D.s⁻¹ * D.t⁻¹ by group]
      exact mul_mem (mul_mem (hT₁ h1) (inv_mem hs)) (inv_mem ht)

theorem exists_p (hsylZ : SylZInput D) {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F)
    [IsMulCommutative ↥F] {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F)
    {k : NBar.Q F} (hk : Odd (orderOf k))
    (hk₀ : k * NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ =
      NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ * k)
    (hk₁ : k * NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ =
      NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ * k) {v : ↥F}
    (hv₀ : NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) v = v)
    (hv₁ : NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) v = v)
    (hkv : NBar.ρ F k v ≠ v) :
    ∃ p : G, p ∈ normalizer (D.T₁ : Set G) ∧ Odd (orderOf p) ∧ p * v * p⁻¹ ≠ v := by
  classical
  haveI := hF.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁) with hZ
  have hZF : Z ≤ F := Z_le_E64 D hF
  have hW := fix_iff_mem_Z D hF hd₀ hd₀F hd₁ hd₁F
  have hvZ : (v : G) ∈ Z := (hW v).1 ⟨hv₀, hv₁⟩
  obtain ⟨k₀, rfl⟩ := NBar.π_surjective F k
  set d₀N : ↥(normalizer (F : Set G)) := ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩
  set d₁N : ↥(normalizer (F : Set G)) := ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩
  have happ : ∀ {a b : NBar.Q F}, a * b = b * a → ∀ w : ↥F,
      NBar.ρ F a (NBar.ρ F b w) = NBar.ρ F b (NBar.ρ F a w) := fun hab w => by
    rw [← MulAut.mul_apply, ← map_mul, hab, map_mul, MulAut.mul_apply]
  have hk₀Z : ∀ z ∈ Z, (k₀ : G) * z * (k₀ : G)⁻¹ ∈ Z := by
    intro z hz
    obtain ⟨h0, h1⟩ := (hW ⟨z, hZF hz⟩).2 hz
    have h := (hW (NBar.ρ F (NBar.π F k₀) ⟨z, hZF hz⟩)).1
      ⟨by rw [happ hk₀.symm, h0], by rw [happ hk₁.symm, h1]⟩
    rwa [NBar.ρ_π] at h
  set K := centralizer (Z : Set G) with hK
  obtain ⟨P, hP⟩ := hsylZ
  have hT₁K : D.T₁ ≤ K := fun y hy =>
    mem_centralizer_iff.2 fun z hz => (comm_of_mem_T₁_of_mem_Z D hy hz).symm
  have hk₀K : ∀ c ∈ K, (k₀ : G) * c * (k₀ : G)⁻¹ ∈ K := by
    intro c hc
    have hk₀N : (k₀ : G)⁻¹ ∈ normalizer (Z : Set G) :=
      inv_mem (TStruct.mem_normalizer_of_forall_conj_mem hk₀Z)
    refine mem_centralizer_iff.2 fun z hz => ?_
    have hz' : (k₀ : G)⁻¹ * z * (k₀ : G)⁻¹⁻¹ ∈ Z := (mem_normalizer_iff.1 hk₀N z).1 hz
    rw [inv_inv] at hz'
    have h1 := (mem_centralizer_iff.1 hc) _ hz'
    calc z * ((k₀ : G) * c * (k₀ : G)⁻¹)
        = (k₀ : G) * (((k₀ : G)⁻¹ * z * k₀) * c) * (k₀ : G)⁻¹ := by group
      _ = (k₀ : G) * (c * ((k₀ : G)⁻¹ * z * k₀)) * (k₀ : G)⁻¹ := by rw [h1]
      _ = (k₀ : G) * c * (k₀ : G)⁻¹ * z := by group
  set T₁' := D.T₁.map (MulAut.conj (k₀ : G)).toMonoidHom with hT₁'
  have hT₁'K : T₁' ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hk₀K y (hT₁K hy)
  have hT₁2 : IsPGroup 2 D.T₁ := T.isPGroup'.to_le D.T₁_le_T
  have hP2 : IsPGroup 2 (T₁'.subgroupOf K) := (hT₁2.map _).comap_subtype
  obtain ⟨c, hc⟩ := exists_conj_mem_of_isPGroup P hP2
  set y : G := (c : G) * k₀ with hy
  have hyT₁ : ∀ x ∈ D.T₁, y * x * y⁻¹ ∈ D.T₁ := by
    intro x hx
    have hmem : (⟨(k₀ : G) * x * (k₀ : G)⁻¹, hT₁'K ⟨x, hx, rfl⟩⟩ : ↥K) ∈ T₁'.subgroupOf K := by
      rw [mem_subgroupOf]
      exact ⟨x, hx, rfl⟩
    have h1 := hc _ hmem
    have h1' : c * ⟨(k₀ : G) * x * (k₀ : G)⁻¹, hT₁'K ⟨x, hx, rfl⟩⟩ * c⁻¹ ∈ (P : Subgroup ↥K) := h1
    rw [hP, mem_subgroupOf] at h1'
    convert h1' using 1
    simp only [hy, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hyN : y ∈ normalizer (D.T₁ : Set G) := TStruct.mem_normalizer_of_forall_conj_mem hyT₁
  have hyZ : ∀ z ∈ Z, y * z * y⁻¹ = (k₀ : G) * z * (k₀ : G)⁻¹ := by
    intro z hz
    have hcz := (mem_centralizer_iff.1 c.2) _ (hk₀Z z hz)
    calc y * z * y⁻¹ = (c : G) * ((k₀ : G) * z * (k₀ : G)⁻¹) * (c : G)⁻¹ := by
          rw [hy]; group
      _ = (k₀ : G) * z * (k₀ : G)⁻¹ := by rw [← hcz, mul_inv_cancel_right]
  have hyj : ∀ j : ℕ, ∀ z ∈ Z, y ^ j * z * (y ^ j)⁻¹ = (k₀ : G) ^ j * z * ((k₀ : G) ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro z _; simp
    | succ j ih =>
      intro z hz
      calc y ^ (j + 1) * z * (y ^ (j + 1))⁻¹ = y ^ j * (y * z * y⁻¹) * (y ^ j)⁻¹ := by group
        _ = y ^ j * ((k₀ : G) * z * (k₀ : G)⁻¹) * (y ^ j)⁻¹ := by rw [hyZ z hz]
        _ = (k₀ : G) ^ j * ((k₀ : G) * z * (k₀ : G)⁻¹) * ((k₀ : G) ^ j)⁻¹ := ih _ (hk₀Z z hz)
        _ = (k₀ : G) ^ (j + 1) * z * ((k₀ : G) ^ (j + 1))⁻¹ := by group
  set o := orderOf (NBar.π F k₀) with ho
  have hk₀o : (k₀ : G) ^ o * (v : G) * ((k₀ : G) ^ o)⁻¹ = v := by
    have h1 : NBar.π F (k₀ ^ o) = 1 := by rw [map_pow, ho, pow_orderOf_eq_one]
    rw [NBar.π_eq_one_iff] at h1
    have := h1 v v.2
    rwa [Subgroup.coe_pow] at this
  have hyo : y ^ o * v * (y ^ o)⁻¹ = v := by rw [hyj o v hvZ, hk₀o]
  obtain ⟨a, N', hN'odd, hN⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  set p := y ^ (2 ^ a) with hp
  have hpodd : Odd (orderOf p) := by
    rw [hp, orderOf_pow_of_dvd (by positivity) (by rw [hN]; exact Dvd.intro N' rfl), hN,
      Nat.mul_div_cancel_left _ (by positivity)]
    exact hN'odd
  refine ⟨p, pow_mem hyN _, hpodd, fun hpv => hkv ?_⟩
  have hcop : Nat.Coprime (2 ^ a) o := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hk)
  have hyC : y ∈ centralizer ({(v : G)} : Set G) := mem_of_pow_mem_of_coprime
    (mem_centralizer_singleton_iff.2 (by
      calc y ^ 2 ^ a * (v : G) = (y ^ 2 ^ a * v * (y ^ 2 ^ a)⁻¹) * y ^ 2 ^ a := by group
        _ = v * y ^ 2 ^ a := by rw [← hp, hpv]))
    (mem_centralizer_singleton_iff.2 (by
      calc y ^ o * (v : G) = (y ^ o * v * (y ^ o)⁻¹) * y ^ o := by group
        _ = v * y ^ o := by rw [hyo]))
    hcop
  have hyv : y * v * y⁻¹ = v := by
    rw [mem_centralizer_singleton_iff.1 hyC, mul_inv_cancel_right]
  refine Subtype.ext ?_
  rw [NBar.ρ_π, ← hyZ v hvZ, hyv]

theorem lemma10 (hnA : ¬ StronglyInvolutionClosed D.A (T : Subgroup G))
    (hnAs : ¬ StronglyInvolutionClosed D.Astar (T : Subgroup G)) (hHig : HigmanHyp)
    (hSylN : SylNInput (T : Subgroup G)) (hTv : TvInput D) (hquot : QuotInput (T : Subgroup G))
    (hswap : SwapInput D) (hsylZ : SylZInput D) (hT₁ : Nonempty (↥D.T₁ ≃* X 2 n n))
    (hL4 : Lemma4Input D) (hL5 : Lemma5Input (T : Subgroup G))
    {F : Subgroup G} (hF : IsE64 (T : Subgroup G) F) [IsMulCommutative ↥F] {d₀ d₁ : G}
    (hd₀ : d₀ ∈ D.B₀ ⊓ normalizer ((F ⊓ D.B₀ : Subgroup G) : Set G)) (hd₀F : d₀ ∉ F)
    (hd₁ : d₁ ∈ D.B₁ ⊓ normalizer ((F ⊓ D.B₁ : Subgroup G) : Set G)) (hd₁F : d₁ ∉ F) :
    ∀ k : NBar.Q F, Odd (orderOf k) →
      k * NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ =
        NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩ * k →
      k * NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ =
        NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩ * k →
      ∀ v : ↥F, NBar.ρ F (NBar.π F ⟨d₀, D.mem_normalizer_of_mem_R₀ hF hd₀⟩) v = v →
        NBar.ρ F (NBar.π F ⟨d₁, D.mem_normalizer_of_mem_R₁ hF hd₁⟩) v = v →
        NBar.ρ F k v = v := by
  intro k hk hk₀ hk₁ v hv₀ hv₁
  by_contra hkv
  obtain ⟨p, hpN, hpodd, hpv⟩ := exists_p D hsylZ hF hd₀ hd₀F hd₁ hd₁F hk hk₀ hk₁ hv₀ hv₁ hkv
  have hvZ := (fix_iff_mem_Z D hF hd₀ hd₀F hd₁ hd₁F v).1 ⟨hv₀, hv₁⟩
  have hmove : ∃ z ∈ D.A ⊔ (zpowers D.b₀ ⊔ zpowers D.b₁), p * z * p⁻¹ ≠ z := ⟨v, hvZ, hpv⟩
  obtain ⟨hcube, hcomm⟩ := lemma1_T₁ D hT₁ hpN hpodd ⟨v, D.le_T₁_of_isE64 hF v.2, hpv⟩
  have hTN := le_normalizer_commZ D hHig hSylN hTv hquot hswap hcube hcomm hmove hF
  have hA₀ := eq_A_or_eq_Astar D (commZ_le_Z D hcomm) (card_commZ D hF hcomm hcube hmove)
    (commZ_inf D hF hcomm hcube)
    (fun x hx => (mem_normalizer_iff.1 (hTN (D.B_le_T D.s_mem_B)) x).1 hx)
    (fun x hx => (mem_normalizer_iff.1 (hTN D.t_mem_T) x).1 hx)
  have haA₀ : D.a ∈ commZ D p := by
    rcases hA₀ with h | h <;> rw [h]
    · exact D.a_mem
    · exact D.a_mem_Astar
  have hnSIC : ¬ StronglyInvolutionClosed (commZ D p) (T : Subgroup G) := by
    rcases hA₀ with h | h <;> rw [h]
    · exact hnA
    · exact hnAs
  have hconjA₀ : ∀ k' ∈ commZ D p, k' ≠ 1 → ∃ q : G, k' = q * D.a * q⁻¹ := by
    intro k' hk' hk'1
    haveI := hF.finite
    have hV : ∀ w : ↥F, w * w = 1 := fun w => Subtype.ext (hF.mul_self w w.2)
    have hx3 := ρ_pbar_pow_three D hF hcomm hcube
    have hcardU := card_commZ D hF hcomm hcube hmove
    rw [← map_commV_pbar D hF hcomm hcube, card_map_of_injective F.subtype_injective] at hcardU
    have haF := D.a_mem_E64 hF
    have hwU := (mem_commV_iff D hF hcomm hcube ⟨D.a, haF⟩).2 haA₀
    have hw1 : (⟨D.a, haF⟩ : ↥F) ≠ 1 := fun h => D.a_ne_one (congrArg Subtype.val h)
    obtain ⟨hall, -⟩ := mem_commV_zpowers hV hx3 hcardU hwU hw1
    have hk'F : k' ∈ F := Z_le_E64 D hF (commZ_le_Z D hcomm hk')
    have hk'U := (mem_commV_iff D hF hcomm hcube ⟨k', hk'F⟩).2 hk'
    rcases hall _ hk'U with h | h | h | h
    · exact absurd (congrArg Subtype.val h) hk'1
    · have h' : k' = D.a := congrArg Subtype.val h
      exact ⟨1, by rw [h']; group⟩
    · refine ⟨p, ?_⟩
      have h' : k' = ((NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩)
        ⟨D.a, haF⟩ : ↥F) : G) := congrArg Subtype.val h
      rwa [NBar.ρ_π] at h'
    · refine ⟨p * p, ?_⟩
      have h' : k' = ((NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩)
        (NBar.ρ F (NBar.π F ⟨p, mem_normalizer_of_comm D hF hcomm⟩) ⟨D.a, haF⟩) : ↥F) : G) :=
        congrArg Subtype.val h
      rw [NBar.ρ_π, NBar.ρ_π] at h'
      rw [h']
      group
  unfold StronglyInvolutionClosed at hnSIC
  push Not at hnSIC
  obtain ⟨k', hk'A₀, hk'2, g, hgT, hgA₀⟩ := hnSIC
  obtain ⟨q, rfl⟩ := hconjA₀ k' hk'A₀ (fun h => by rw [h, orderOf_one] at hk'2; omega)
  have e : g * (q * D.a * q⁻¹) * g⁻¹ = (g * q) * D.a * (g * q)⁻¹ := by group
  rw [e] at hgT hgA₀
  obtain ⟨y, hyT₁, hyA₀⟩ : ∃ y : G, y * D.a * y⁻¹ ∈ D.T₁ ∧ y * D.a * y⁻¹ ∉ commZ D p := by
    by_cases h : (g * q) * D.a * (g * q)⁻¹ ∈ D.T₁
    · exact ⟨g * q, h, hgA₀⟩
    · obtain ⟨y, hy, hyA, hyAs⟩ := hL4 _ hgT h
      refine ⟨y, hy, ?_⟩
      rcases hA₀ with h' | h' <;> rw [h']
      · exact hyA
      · exact hyAs
  have hx2 : y * D.a * y⁻¹ * (y * D.a * y⁻¹) = 1 := by
    calc y * D.a * y⁻¹ * (y * D.a * y⁻¹) = y * (D.a * D.a) * y⁻¹ := by group
      _ = 1 := by rw [D.a_mul_a, mul_one, mul_inv_cancel]
  obtain ⟨F', hF'T₁, hF'ab, hF'card, hxF'⟩ := D.exists_elem64_of_mem_T₁ hyT₁ hx2
  have hF' : IsE64 (T : Subgroup G) F' := ⟨hF'T₁.trans D.T₁_le_T, hF'ab, hF'card⟩
  have hTC : (T : Subgroup G) ≤ centralizer ({D.a} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.2 (D.a_comm_T hy)
  have hF2 : IsPGroup 2 F' := IsPGroup.of_card hF'card
  obtain ⟨n', hn'N, h, hhT, -, hn'eq⟩ := exists_normalizer_conj (T.subtype hTC)
    (Sylow.coe_subtype T hTC) le_rfl hF2
    (fun u hu w hw => TStruct.comm_of_mul_self hF'.mul_self hu hw) hxF' (hL5 F' hF')
  have hha : h⁻¹ * D.a * h = D.a := by
    rw [mul_assoc, ← D.a_comm_T hhT, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hha] at hn'eq
  have := normalizes_commZ D hHig hSylN hTv hquot hswap hcube hcomm hmove hF' hn'N D.a haA₀
  rw [hn'eq] at this
  exact hyA₀ this

end CFSG.CGT.Foote81L6.Normalizer
