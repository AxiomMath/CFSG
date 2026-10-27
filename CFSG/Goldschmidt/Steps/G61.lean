module

public import CFSG.Goldschmidt.StatementsG2
import CFSG.Walter.Bender1970.S3.Basic
public import CFSG.Goldschmidt.StatementsG

public section

namespace CFSG.Goldschmidt

open CFSG.Walter

namespace G61

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_map_conj_eq [IsSimpleGroup G] {H : Subgroup G} (hH : IsCoatom H) (hH1 : H ≠ ⊥)
    {g : G} (hg : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ H := by
  have hN : Subgroup.normalizer (H : Set G) = H := by
    rcases (hH.le_iff).mp (Subgroup.le_normalizer (H := H)) with h | h
    · exfalso
      have hn : H.Normal := Subgroup.normalizer_eq_top_iff.mp h
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal H with h' | h'
      · exact hH1 h'
      · exact hH.1 h'
    · exact h
  rw [← hN, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have h1 : g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom :=
      ⟨x, hx, by rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
    rwa [hg] at h1
  · intro hx
    rw [← hg] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by
      have := congrArg (fun z => g⁻¹ * z * g) hyx
      simpa [mul_assoc] using this
    rwa [← this]

theorem mem_of_benderM_conj_eq [IsSimpleGroup G] {b n : G} (hb : b ≠ 1) {H : Subgroup G}
    (hH : H ∈ benderM b) (hc : benderM (n⁻¹ * b * n) = {H}) : n ∈ H := by
  have h := map_conj_mem_benderM n⁻¹ hH
  rw [inv_inv, hc, Set.mem_singleton_iff] at h
  have hH1 : H ≠ ⊥ := by
    intro h0
    have hbH := mem_of_mem_benderM hH
    rw [h0, Subgroup.mem_bot] at hbH
    exact hb hbH
  exact (Subgroup.inv_mem_iff H).mp (mem_of_map_conj_eq (isCoatom_of_mem_benderM hH) hH1 h)

omit [Finite G] in
theorem centralizer_le_of_conj {H : Subgroup G} {b n : G} (hn : n ∈ H)
    (h : Subgroup.centralizer ({n⁻¹ * b * n} : Set G) ≤ H) :
    Subgroup.centralizer ({b} : Set G) ≤ H := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : n⁻¹ * x * n ∈ Subgroup.centralizer ({n⁻¹ * b * n} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc n⁻¹ * x * n * (n⁻¹ * b * n) = n⁻¹ * (x * b) * n := by group
      _ = n⁻¹ * (b * x) * n := by rw [hx]
      _ = n⁻¹ * b * n * (n⁻¹ * x * n) := by group
  have hmem := H.mul_mem (H.mul_mem hn (h hx')) (H.inv_mem hn)
  have he : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
  rwa [he] at hmem

theorem false_of_forall_centralizer_le {S : Sylow 2 G} {A : Subgroup G}
    (hset : GoldSetting G S A) {H : Subgroup G} (hH : H ≠ ⊤)
    (h : ∀ b ∈ A, b ≠ 1 → Subgroup.centralizer ({b} : Set G) ≤ H) : False := by
  apply hH
  rw [eq_top_iff, ← hset.gen]
  exact iSup_le fun b => h b.1 b.2.1 b.2.2

omit [Finite G] in
theorem conj_ne_one {x : G} (g : G) (hx : x ≠ 1) : g⁻¹ * x * g ≠ 1 := by
  intro h
  apply hx
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group

end G61

theorem G61_of (h28 : S_G28) : S_G61 := by
  intro G _ _ S A hset a haA ha1 H hH A₁ hA₁A hA₁i hM
  have := hset.isSimpleGroup
  have hHco := isCoatom_of_mem_benderM hH
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hset.elem.2 x hx
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hset.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hMH : ∀ y ∈ A₁, y ≠ 1 → H ∈ benderM y := fun y hy hy1 => by
    rw [hM y hy hy1]
    exact Set.mem_singleton H
  have hconjA : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ x ∈ A, g⁻¹ * x * g ∈ A :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff''.mp hg x).mp hx
  have hidx : ∀ x ∈ A, ∀ y ∈ A, x ∉ A₁ → y ∉ A₁ → x * y ∈ A₁ := by
    intro x hx y hy hxA hyA
    have h := (Subgroup.mul_mem_iff_of_index_two hA₁i (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)).mpr
      (iff_of_false (fun h => hxA (Subgroup.mem_subgroupOf.mp h))
        (fun h => hyA (Subgroup.mem_subgroupOf.mp h)))
    exact Subgroup.mem_subgroupOf.mp h
  have hcardA : Nat.card A = 2 * Nat.card A₁ := by
    have h := (A₁.subgroupOf A).card_mul_index
    rw [hA₁i, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁A).toEquiv] at h
    omega
  have h4 : 4 ≤ Nat.card A := by
    have h2 : 2 ∣ Nat.card A := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have ho : orderOf a = 2 := orderOf_eq_prime (hset.elem.2 a haA) ha1
      exact ho ▸ Subgroup.orderOf_dvd_natCard A haA
    have hne : Nat.card A ≠ 2 := by
      intro hA2
      apply G61.false_of_forall_centralizer_le hset hHco.1
      intro b hb hb1
      obtain ⟨y, -, hyu⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA2
      have e1 := hyu ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
      have e2 := hyu ⟨a, haA⟩ (fun h => ha1 (congrArg Subtype.val h))
      have hba : b = a := congrArg Subtype.val (e1.trans e2.symm)
      rw [hba]
      exact centralizer_le_of_mem_benderM hH
    have hpos : 0 < Nat.card A := Nat.card_pos
    omega
  have hNA : ¬ Subgroup.normalizer (A : Set G) ≤ H := by
    intro hle
    apply G61.false_of_forall_centralizer_le hset hHco.1
    intro b hb hb1
    obtain ⟨n, hnN, hnb⟩ := h28 G A (Subgroup.normalizer (A : Set G)) A₁ hset.elem h4 le_rfl
      hset.irreducible hA₁A hA₁i b hb hb1
    exact G61.centralizer_le_of_conj (hle hnN)
      (centralizer_le_of_mem_benderM (hMH _ hnb (G61.conj_ne_one n hb1)))
  obtain ⟨n, hnN, hnH⟩ := IsConcreteLE.not_le_iff_exists.mp hNA
  have hout : ∀ y ∈ A₁, y ≠ 1 → n⁻¹ * y * n ∉ A₁ := fun y hy hy1 hyn =>
    hnH (G61.mem_of_benderM_conj_eq hy1 (hMH y hy hy1) (hM _ hyn (G61.conj_ne_one n hy1)))
  have huniq : ∀ x ∈ A₁, ∀ y ∈ A₁, x ≠ 1 → y ≠ 1 → x = y := by
    intro x hx y hy hx1 hy1
    by_contra hxy
    have hxy1 : x * y ≠ 1 := by
      intro h
      apply hxy
      calc x = x * (x * y) := by rw [h, mul_one]
        _ = y := by rw [← mul_assoc, hsq x (hA₁A hx), one_mul]
    have h1 := hidx _ (hconjA n hnN x (hA₁A hx)) _ (hconjA n hnN y (hA₁A hy)) (hout x hx hx1)
      (hout y hy hy1)
    have h2 : n⁻¹ * x * n * (n⁻¹ * y * n) = n⁻¹ * (x * y) * n := by group
    rw [h2] at h1
    exact hout _ (A₁.mul_mem hx hy) hxy1 h1
  have hA₁1 : A₁ ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardA
    omega
  obtain ⟨a₁, ha₁, ha₁1⟩ := (A₁.bot_or_exists_ne_one).resolve_left hA₁1
  have hmem₁ : ∀ y ∈ A₁, y = 1 ∨ y = a₁ := fun y hy => by
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (huniq y hy a₁ ha₁ hy1 ha₁1)
  have hA₁eq : A₁ = Subgroup.zpowers a₁ := by
    refine le_antisymm (fun y hy => ?_) (Subgroup.zpowers_le.mpr ha₁)
    rcases hmem₁ y hy with h | h
    · rw [h]
      exact Subgroup.one_mem _
    · rw [h]
      exact Subgroup.mem_zpowers a₁
  have hcard₁ : Nat.card A₁ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hA₁eq, Nat.card_zpowers]
    exact orderOf_eq_prime (hset.elem.2 a₁ (hA₁A ha₁)) ha₁1
  refine ⟨by omega, ?_⟩
  have ha₁a : a₁ = a := by
    by_contra hne
    have hne' : a ≠ a₁ := fun h => hne h.symm
    have hA₁a : a ∉ A₁ := fun h => by
      rcases hmem₁ a h with h | h
      · exact ha1 h
      · exact hne' h
    set c := a * a₁ with hcdef
    have ha₁A := hA₁A ha₁
    have hc : c ∈ A := A.mul_mem haA ha₁A
    have hc1 : c ≠ 1 := by
      intro h
      apply hne'
      calc a = a * (a₁ * a₁) := by rw [hsq a₁ ha₁A, mul_one]
        _ = c * a₁ := by rw [hcdef, mul_assoc]
        _ = a₁ := by rw [h, one_mul]
    have hca : c ≠ a := by
      intro h
      apply ha₁1
      calc a₁ = a * a * a₁ := by rw [hsq a haA, one_mul]
        _ = a * c := by rw [hcdef, mul_assoc]
        _ = 1 := by rw [h, hsq a haA]
    have hac : a₁ = a * c := by rw [hcdef, ← mul_assoc, hsq a haA, one_mul]
    have hcls : ∀ x ∈ A, x ≠ 1 → x ≠ a₁ → x = a ∨ x = c := by
      intro x hx hx1 hxa₁
      have hxA₁ : x ∉ A₁ := fun h => by
        rcases hmem₁ x h with h | h
        · exact hx1 h
        · exact hxa₁ h
      have hxa := hidx x hx a haA hxA₁ hA₁a
      rcases hmem₁ _ hxa with h | h
      · left
        calc x = x * a * a := by rw [mul_assoc, hsq a haA, mul_one]
          _ = a := by rw [h, one_mul]
      · right
        calc x = x * a * a := by rw [mul_assoc, hsq a haA, mul_one]
          _ = a₁ * a := by rw [h]
          _ = c := by rw [hcdef, hcomm a₁ ha₁A a haA]
    have hF1 : ∀ u : G, u⁻¹ * a * u = a₁ → u ∈ H := fun u hu =>
      G61.mem_of_benderM_conj_eq ha1 hH (by rw [hu]; exact hM a₁ ha₁ ha₁1)
    have hF2 : ∀ u ∈ H, u⁻¹ * c * u = a ∨ u⁻¹ * c * u = a₁ → False := by
      intro u hu h
      apply G61.false_of_forall_centralizer_le hset hHco.1
      have hCa : Subgroup.centralizer ({a} : Set G) ≤ H := centralizer_le_of_mem_benderM hH
      have hCa₁ : Subgroup.centralizer ({a₁} : Set G) ≤ H :=
        centralizer_le_of_mem_benderM (hMH a₁ ha₁ ha₁1)
      have hCc : Subgroup.centralizer ({c} : Set G) ≤ H := by
        refine G61.centralizer_le_of_conj hu ?_
        rcases h with h | h
        · rw [h]; exact hCa
        · rw [h]; exact hCa₁
      intro x hx hx1
      by_cases hxa₁ : x = a₁
      · rw [hxa₁]; exact hCa₁
      · rcases hcls x hx hx1 hxa₁ with h | h
        · rw [h]; exact hCa
        · rw [h]; exact hCc
    have hmulc : ∀ u : G, u⁻¹ * a₁ * u = u⁻¹ * a * u * (u⁻¹ * c * u) := fun u => by
      rw [hac]; group
    obtain ⟨t, htN, hta⟩ := h28 G A (Subgroup.normalizer (A : Set G)) A₁ hset.elem h4 le_rfl
      hset.irreducible hA₁A hA₁i a haA ha1
    have hta' : t⁻¹ * a * t = a₁ := huniq _ hta _ ha₁ (G61.conj_ne_one t ha1) ha₁1
    have htH := hF1 t hta'
    have htc : t⁻¹ * c * t = c := by
      rcases hcls _ (hconjA t htN c hc) (G61.conj_ne_one t hc1)
          (fun h => hF2 t htH (Or.inr h)) with h | h
      · exact absurd (Or.inl h) (hF2 t htH)
      · exact h
    have hta₁ : t⁻¹ * a₁ * t = a := by
      rw [hmulc, hta', htc, hcdef, ← mul_assoc, hcomm a₁ ha₁A a haA, mul_assoc,
        hsq a₁ ha₁A, mul_one]
    obtain ⟨s, hsN, hsc⟩ := h28 G A (Subgroup.normalizer (A : Set G)) A₁ hset.elem h4 le_rfl
      hset.irreducible hA₁A hA₁i c hc hc1
    have hsc' : s⁻¹ * c * s = a₁ := huniq _ hsc _ ha₁ (G61.conj_ne_one s hc1) ha₁1
    have hsa₁ : s⁻¹ * a * s ≠ a₁ := by
      intro h
      apply hca
      have h' : s⁻¹ * c * s = s⁻¹ * a * s := hsc'.trans h.symm
      have := congrArg (fun z => s * z * s⁻¹) h'
      simpa [mul_assoc] using this
    rcases hcls _ (hconjA s hsN a haA) (G61.conj_ne_one s ha1) hsa₁ with hsa | hsa
    ·
      have hu1 : (s * t)⁻¹ * a * (s * t) = a₁ := by
        rw [show (s * t)⁻¹ * a * (s * t) = t⁻¹ * (s⁻¹ * a * s) * t by group, hsa, hta']
      have hu2 : (s * t)⁻¹ * c * (s * t) = a := by
        rw [show (s * t)⁻¹ * c * (s * t) = t⁻¹ * (s⁻¹ * c * s) * t by group, hsc', hta₁]
      exact hF2 _ (hF1 _ hu1) (Or.inl hu2)
    ·
      have hsa₁' : s⁻¹ * a₁ * s = a := by
        rw [hmulc, hsa, hsc', hcdef, mul_assoc, hsq a₁ ha₁A, mul_one]
      have hu1 : (s * s)⁻¹ * a * (s * s) = a₁ := by
        rw [show (s * s)⁻¹ * a * (s * s) = s⁻¹ * (s⁻¹ * a * s) * s by group, hsa, hsc']
      have hu2 : (s * s)⁻¹ * c * (s * s) = a := by
        rw [show (s * s)⁻¹ * c * (s * s) = s⁻¹ * (s⁻¹ * c * s) * s by group, hsc', hsa₁']
      exact hF2 _ (hF1 _ hu1) (Or.inl hu2)
  rw [hA₁eq, ha₁a]

end CFSG.Goldschmidt
