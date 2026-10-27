module

public import CFSG.GH74.QTGen4.U42.MSplit
public import CFSG.Quasithin.H13.A5S1517
public import CFSG.GH74.QTGen4.U42.MSplitB

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.A5Model CFSG.Blueprint
open CFSG.Quasithin.H13 CFSG.Quasithin.H13.A5

theorem sup_decomp {G : Type} [Group G] {T L : Subgroup G}
    (hN : ∀ q : G, q ∈ L ⊔ T → ∀ l ∈ L, q * l * q⁻¹ ∈ L) {q : G} (hq : q ∈ L ⊔ T) :
    ∃ y ∈ T, ∃ z ∈ L, y * z = q := by
  let P : Subgroup G :=
    { carrier := {g | ∃ y ∈ T, ∃ z ∈ L, y * z = g}
      one_mem' := ⟨1, T.one_mem, 1, L.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨y1, hy1, z1, hz1, rfl⟩ ⟨y2, hy2, z2, hz2, rfl⟩
        have hc : y2⁻¹ * z1 * y2 ∈ L := by
          have := hN y2⁻¹ (Subgroup.mem_sup_right (T.inv_mem hy2)) z1 hz1
          simpa using this
        exact ⟨y1 * y2, T.mul_mem hy1 hy2, y2⁻¹ * z1 * y2 * z2, L.mul_mem hc hz2, by group⟩
      inv_mem' := by
        rintro _ ⟨y, hy, z, hz, rfl⟩
        exact ⟨y⁻¹, T.inv_mem hy, y * z⁻¹ * y⁻¹, hN y (Subgroup.mem_sup_right hy) z⁻¹
          (L.inv_mem hz), by group⟩ }
  have hP : L ⊔ T ≤ P := sup_le (fun l hl => ⟨1, T.one_mem, l, hl, by simp⟩)
    (fun t ht => ⟨t, ht, 1, L.one_mem, by simp⟩)
  obtain ⟨y, hy, z, hz, h⟩ : ∃ y ∈ T, ∃ z ∈ L, y * z = q := hP hq
  exact ⟨y, hy, z, hz, h⟩

theorem relIndex_eq_of_normal {G : Type} [Group G] [Finite G] {T L : Subgroup G}
    (hN : ∀ q : G, q ∈ L ⊔ T → ∀ l ∈ L, q * l * q⁻¹ ∈ L) :
    T.relIndex L = T.relIndex (L ⊔ T) := by
  have hTQ : T ≤ L ⊔ T := le_sup_right
  have hLQ : L ≤ L ⊔ T := le_sup_left
  have hKn : (L.subgroupOf (L ⊔ T)).Normal := ⟨fun n hn g =>
    Subgroup.mem_subgroupOf.mpr (by simpa using hN g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hsup : T.subgroupOf (L ⊔ T) ⊔ L.subgroupOf (L ⊔ T) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨q, hq⟩ _
    obtain ⟨y, hy, z, hz, rfl⟩ := sup_decomp hN hq
    have e : (⟨y * z, hq⟩ : ↥(L ⊔ T)) = ⟨y, hTQ hy⟩ * ⟨z, hLQ hz⟩ := Subtype.ext rfl
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hy))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hz))
  have hF3 : L.relIndex (L ⊔ T) = L.relIndex T := by
    have h1 := Subgroup.relIndex_sup_right (T.subgroupOf (L ⊔ T)) (L.subgroupOf (L ⊔ T))
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 : (L.subgroupOf (L ⊔ T)).relIndex (T.subgroupOf (L ⊔ T)) = L.relIndex T :=
      Subgroup.relIndex_subgroupOf hTQ
    show (L.subgroupOf (L ⊔ T)).index = L.relIndex T
    rw [h1, h2]
  have hF1 := Subgroup.relIndex_inf_mul_relIndex L T (L ⊔ T)
  have hF2 := Subgroup.relIndex_inf_mul_relIndex T L (L ⊔ T)
  rw [inf_eq_left.mpr hTQ] at hF1
  rw [inf_eq_left.mpr hLQ] at hF2
  rw [inf_comm L T] at hF1
  rw [hF3] at hF2
  have hpos : L.relIndex T ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have key : L.relIndex T * T.relIndex (L ⊔ T) = L.relIndex T * T.relIndex L := by
    rw [hF1, ← hF2]
    ring
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos) key).symm

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : A5.Setting G T L V)
include S

theorem exists_K4_lift_L (hVL : V ≤ L) (hTV : T ⊓ Subgroup.centralizer (V : Set G) ≤ V) :
    ∃ (a b : G) (ha : a ∈ Subgroup.normalizer (V : Set G))
      (hb : b ∈ Subgroup.normalizer (V : Set G)), a ∈ T ⊓ L ∧ b ∈ T ⊓ L ∧
      S.frame.ρ ⟨a, ha⟩ = pa ∧ S.frame.ρ ⟨b, hb⟩ = pb ∧ a * a = 1 ∧ b * b = 1 ∧
      a * b = b * a := by
  classical
  set N := Subgroup.normalizer (V : Set G) with hNdef
  have hVN : V ≤ N := Subgroup.le_normalizer
  have hρmul : ∀ (x y : G) (hx : x ∈ N) (hy : y ∈ N),
      S.frame.ρ ⟨x * y, N.mul_mem hx hy⟩ = S.frame.ρ ⟨x, hx⟩ * S.frame.ρ ⟨y, hy⟩ := by
    intro x y hx hy
    rw [← map_mul]
    rfl
  have hρinv : ∀ (x : G) (hx : x ∈ N),
      S.frame.ρ ⟨x⁻¹, N.inv_mem hx⟩ = (S.frame.ρ ⟨x, hx⟩)⁻¹ := by
    intro x hx
    rw [← map_inv]
    rfl
  have hker : ∀ (g : G) (hg : g ∈ N), g ∈ T → S.frame.ρ ⟨g, hg⟩ = 1 → g ∈ V :=
    fun g hg hgT h1 => hTV ⟨hgT, S.frame.mem_centralizer_of_rho ⟨g, hg⟩ h1⟩
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have := S.elemAbelian_V.2 v hv
    rwa [pow_two] at this
  obtain ⟨hpa2, hpb2, hpab⟩ := K4_facts
  obtain ⟨⟨a₀, ha₀N⟩, ha₀TL, ha₀⟩ := S.K4_TL pa (Or.inr (Or.inl rfl))
  simp only at ha₀TL
  have hs : a₀ * a₀ ∈ V :=
    hker _ (N.mul_mem ha₀N ha₀N) (T.mul_mem ha₀TL.1 ha₀TL.1)
      (by rw [hρmul a₀ a₀ ha₀N ha₀N, ha₀, hpa2])
  have hsfix : pact (S.frame.ρ ⟨a₀, ha₀N⟩) (S.frame.ψ ⟨a₀ * a₀, hs⟩) =
      S.frame.ψ ⟨a₀ * a₀, hs⟩ := by
    refine (S.conj_eq_iff ⟨a₀, ha₀N⟩ ⟨a₀ * a₀, hs⟩).1 ?_
    show a₀ * (a₀ * a₀) * a₀⁻¹ = a₀ * a₀
    group
  rw [ha₀] at hsfix
  obtain ⟨u₀, hu₀⟩ := fix_pa_eq _ hsfix
  rw [← ha₀] at hu₀
  have hs' := eq_mul_conj_of_psi S ⟨a₀, ha₀N⟩ hs hu₀
  obtain ⟨u, hu⟩ : ∃ u : G, u = (S.frame.ψ.symm u₀ : G) := ⟨_, rfl⟩
  rw [← hu] at hs'
  have huV : u ∈ V := hu ▸ (S.frame.ψ.symm u₀).2
  obtain ⟨a, ha_def⟩ : ∃ a : G, a = u * a₀ := ⟨_, rfl⟩
  have haN : a ∈ N := ha_def ▸ N.mul_mem (hVN huV) ha₀N
  have haT : a ∈ T := ha_def ▸ T.mul_mem (S.V_le_T huV) ha₀TL.1
  have haL : a ∈ L := ha_def ▸ L.mul_mem (hVL huV) ha₀TL.2
  have haρ : S.frame.ρ ⟨a, haN⟩ = pa := by
    subst ha_def
    rw [hρmul u a₀ (hVN huV) ha₀N, rho_V S huV, one_mul, ha₀]
  have ha2 : a * a = 1 := by
    calc a * a = (u * (a₀ * u * a₀⁻¹)) * (a₀ * a₀) := by rw [ha_def]; group
      _ = (a₀ * a₀) * (a₀ * a₀) := by rw [← hs']
      _ = 1 := hsq _ hs
  obtain ⟨⟨b₀, hb₀N⟩, hb₀TL, hb₀⟩ := S.K4_TL pb (Or.inr (Or.inr (Or.inl rfl)))
  simp only at hb₀TL
  obtain ⟨w, hw_def⟩ : ∃ w : G, w = b₀ * a * b₀⁻¹ * a⁻¹ := ⟨_, rfl⟩
  have hwN : w ∈ N := hw_def ▸
    N.mul_mem (N.mul_mem (N.mul_mem hb₀N haN) (N.inv_mem hb₀N)) (N.inv_mem haN)
  have hwT : w ∈ T := hw_def ▸ T.mul_mem (T.mul_mem (T.mul_mem hb₀TL.1 haT)
    (T.inv_mem hb₀TL.1)) (T.inv_mem haT)
  have hwV : w ∈ V := by
    refine hker w hwN hwT ?_
    subst hw_def
    rw [hρmul _ _ (N.mul_mem (N.mul_mem hb₀N haN) (N.inv_mem hb₀N)) (N.inv_mem haN),
      hρmul _ _ (N.mul_mem hb₀N haN) (N.inv_mem hb₀N), hρmul _ _ hb₀N haN, hρinv _ hb₀N,
      hρinv _ haN, hb₀, haρ, hpab]
  have hwa : a * w * a⁻¹ = w := by
    have h1 : (w * a) * (w * a) = 1 := by
      calc (w * a) * (w * a) = b₀ * (a * a) * b₀⁻¹ := by rw [hw_def]; group
        _ = 1 := by rw [ha2]; group
    have h2 : a * w * a⁻¹ = w⁻¹ := by
      calc a * w * a⁻¹ = w⁻¹ * ((w * a) * (w * a)) * (a * a)⁻¹ := by group
        _ = w⁻¹ := by rw [h1, ha2]; group
    rw [h2]
    exact inv_eq_of_mul_eq_one_right (hsq w hwV)
  have hwfix : pact (S.frame.ρ ⟨a, haN⟩) (S.frame.ψ ⟨w, hwV⟩) = S.frame.ψ ⟨w, hwV⟩ :=
    (S.conj_eq_iff ⟨a, haN⟩ ⟨w, hwV⟩).1 hwa
  rw [haρ] at hwfix
  obtain ⟨y₀, hy₀⟩ := fix_pa_eq _ hwfix
  rw [← haρ] at hy₀
  have hw' := eq_mul_conj_of_psi S ⟨a, haN⟩ hwV hy₀
  obtain ⟨y, hy⟩ : ∃ y : G, y = (S.frame.ψ.symm y₀ : G) := ⟨_, rfl⟩
  rw [← hy] at hw'
  have hyV : y ∈ V := hy ▸ (S.frame.ψ.symm y₀).2
  obtain ⟨b₁, hb₁_def⟩ : ∃ b₁ : G, b₁ = y * b₀ := ⟨_, rfl⟩
  have hb₁N : b₁ ∈ N := hb₁_def ▸ N.mul_mem (hVN hyV) hb₀N
  have hb₁T : b₁ ∈ T := hb₁_def ▸ T.mul_mem (S.V_le_T hyV) hb₀TL.1
  have hb₁L : b₁ ∈ L := hb₁_def ▸ L.mul_mem (hVL hyV) hb₀TL.2
  have hb₁ρ : S.frame.ρ ⟨b₁, hb₁N⟩ = pb := by
    subst hb₁_def
    rw [hρmul y b₀ (hVN hyV) hb₀N, rho_V S hyV, one_mul, hb₀]
  have hb₁a : b₁ * a = a * b₁ := by
    have hb₀a : b₀ * a = w * a * b₀ := by rw [hw_def]; group
    calc b₁ * a = y * (b₀ * a) := by rw [hb₁_def]; group
      _ = y * (y * (a * y * a⁻¹)) * a * b₀ := by rw [hb₀a, hw']; group
      _ = (y * y) * (a * y * a⁻¹) * a * b₀ := by group
      _ = a * b₁ := by rw [hsq y hyV, hb₁_def]; group
  obtain ⟨t, ht_def⟩ : ∃ t : G, t = b₁ * b₁ := ⟨_, rfl⟩
  have htV : t ∈ V := by
    refine hker t (ht_def ▸ N.mul_mem hb₁N hb₁N) (ht_def ▸ T.mul_mem hb₁T hb₁T) ?_
    subst ht_def
    rw [hρmul _ _ hb₁N hb₁N, hb₁ρ, hpb2]
  have hconj : a * b₁ * a⁻¹ = b₁ := by rw [← hb₁a]; group
  have hta : a * t * a⁻¹ = t := by
    calc a * t * a⁻¹ = (a * b₁ * a⁻¹) * (a * b₁ * a⁻¹) := by rw [ht_def]; group
      _ = t := by rw [hconj, ht_def]
  have htb : b₁ * t * b₁⁻¹ = t := by rw [ht_def]; group
  have htfa : pact pa (S.frame.ψ ⟨t, htV⟩) = S.frame.ψ ⟨t, htV⟩ := by
    rw [← haρ]
    exact (S.conj_eq_iff ⟨a, haN⟩ ⟨t, htV⟩).1 hta
  have htfb : pact pb (S.frame.ψ ⟨t, htV⟩) = S.frame.ψ ⟨t, htV⟩ := by
    rw [← hb₁ρ]
    exact (S.conj_eq_iff ⟨b₁, hb₁N⟩ ⟨t, htV⟩).1 htb
  obtain ⟨x₀, hx₀a, hx₀⟩ := fix_pa_pb_eq _ htfa htfb
  rw [← hb₁ρ] at hx₀
  have ht' := eq_mul_conj_of_psi S ⟨b₁, hb₁N⟩ htV hx₀
  obtain ⟨x, hx⟩ : ∃ x : G, x = (S.frame.ψ.symm x₀ : G) := ⟨_, rfl⟩
  rw [← hx] at ht'
  have hxV : x ∈ V := hx ▸ (S.frame.ψ.symm x₀).2
  have hxa : a * x = x * a := by
    have h1 : a * x * a⁻¹ = x := by
      refine (S.conj_eq_iff ⟨a, haN⟩ ⟨x, hxV⟩).2 ?_
      have e : (⟨x, hxV⟩ : ↥V) = S.frame.ψ.symm x₀ := Subtype.ext hx
      rw [e, MulEquiv.apply_symm_apply, haρ]
      exact hx₀a
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  obtain ⟨b, hb_def⟩ : ∃ b : G, b = x * b₁ := ⟨_, rfl⟩
  have hbN : b ∈ N := hb_def ▸ N.mul_mem (hVN hxV) hb₁N
  have hbT : b ∈ T := hb_def ▸ T.mul_mem (S.V_le_T hxV) hb₁T
  have hbL : b ∈ L := hb_def ▸ L.mul_mem (hVL hxV) hb₁L
  have hbρ : S.frame.ρ ⟨b, hbN⟩ = pb := by
    subst hb_def
    rw [hρmul x b₁ (hVN hxV) hb₁N, rho_V S hxV, one_mul, hb₁ρ]
  have hb2 : b * b = 1 := by
    calc b * b = (x * (b₁ * x * b₁⁻¹)) * (b₁ * b₁) := by rw [hb_def]; group
      _ = t * t := by rw [← ht', ← ht_def]
      _ = 1 := hsq t htV
  have hab : a * b = b * a := by
    calc a * b = (a * x) * b₁ := by rw [hb_def]; group
      _ = x * (b₁ * a) := by rw [hxa, hb₁a]; group
      _ = b * a := by rw [hb_def]; group
  exact ⟨a, b, haN, hbN, Subgroup.mem_inf.mpr ⟨haT, haL⟩, Subgroup.mem_inf.mpr ⟨hbT, hbL⟩,
    haρ, hbρ, ha2, hb2, hab⟩

theorem L_splits (hVL : V ≤ L) (hO : pCoreOf 2 (L ⊔ T) = V) :
    ∃ A : Subgroup G, A ≤ L ∧ A ⊓ V = ⊥ ∧ V ⊔ A = L := by
  classical
  have hTV : T ⊓ Subgroup.centralizer (V : Set G) ≤ V := le_of_eq (S.cT.trans hO)
  obtain ⟨a, b, haN, hbN, haTL, hbTL, hρa, hρb, ha2, hb2, hab⟩ := exists_K4_lift_L S hVL hTV
  have haT : a ∈ T := (Subgroup.mem_inf.mp haTL).1
  have haL : a ∈ L := (Subgroup.mem_inf.mp haTL).2
  have hbT : b ∈ T := (Subgroup.mem_inf.mp hbTL).1
  have hbL : b ∈ L := (Subgroup.mem_inf.mp hbTL).2
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer S.T_le_NL
  have hN : ∀ q : G, q ∈ L ⊔ T → ∀ l ∈ L, q * l * q⁻¹ ∈ L := fun q hq l hl =>
    (Subgroup.mem_normalizer_iff.mp (hLTN hq) l).mp hl
  have hρab : S.frame.ρ ⟨a * b, (Subgroup.normalizer (V : Set G)).mul_mem haN hbN⟩ = pa * pb := by
    rw [← hρa, ← hρb, ← map_mul]
    rfl
  have hK0TL : klein a b ha2 hb2 hab ≤ T ⊓ L := by
    intro x hx
    rcases (mem_klein_iff a b ha2 hb2 hab x).1 hx with h | h | h | h
    · rw [h]; exact (T ⊓ L).one_mem
    · rw [h]; exact Subgroup.mem_inf.mpr ⟨haT, haL⟩
    · rw [h]; exact Subgroup.mem_inf.mpr ⟨hbT, hbL⟩
    · rw [h]; exact (T ⊓ L).mul_mem (Subgroup.mem_inf.mpr ⟨haT, haL⟩)
        (Subgroup.mem_inf.mpr ⟨hbT, hbL⟩)
  have hK0V : V ⊓ klein a b ha2 hb2 hab = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxK⟩
    rcases (mem_klein_iff a b ha2 hb2 hab x).1 hxK with h | h | h | h
    · rw [h]; exact Subgroup.mem_bot.mpr rfl
    · exfalso
      rw [h] at hxV
      have h1 : pa = 1 := by rw [← hρa]; exact rho_V S hxV
      exact absurd h1 (by decide)
    · exfalso
      rw [h] at hxV
      have h1 : pb = 1 := by rw [← hρb]; exact rho_V S hxV
      exact absurd h1 (by decide)
    · exfalso
      rw [h] at hxV
      have h1 : pa * pb = 1 := by rw [← hρab]; exact rho_V S hxV
      exact absurd h1 (by decide)
  have hfac : ∀ (t : G) (ht : t ∈ T) (hNt : t ∈ Subgroup.normalizer (V : Set G)) (k : G)
      (hk : k ∈ T) (hkN : k ∈ Subgroup.normalizer (V : Set G)),
      S.frame.ρ ⟨t, hNt⟩ = S.frame.ρ ⟨k, hkN⟩ → t * k⁻¹ ∈ V := by
    intro t ht hNt k hk hkN hρk
    have hwN : t * k⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).mul_mem hNt ((Subgroup.normalizer (V : Set G)).inv_mem hkN)
    have e : S.frame.ρ ⟨t * k⁻¹, hwN⟩ = S.frame.ρ ⟨t, hNt⟩ * (S.frame.ρ ⟨k, hkN⟩)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    have h1 : S.frame.ρ ⟨t * k⁻¹, hwN⟩ = 1 := by
      rw [e, hρk, mul_inv_cancel]
    have hwT : t * k⁻¹ ∈ T := T.mul_mem ht (T.inv_mem hk)
    exact hTV ⟨hwT, S.frame.mem_centralizer_of_rho ⟨t * k⁻¹, hwN⟩ h1⟩
  have hdec : ∀ t ∈ T ⊓ L, ∃ v ∈ V, ∃ k ∈ klein a b ha2 hb2 hab, v * k = t := by
    intro t htTL
    have htT : t ∈ T := (Subgroup.mem_inf.mp htTL).1
    have htL : t ∈ L := (Subgroup.mem_inf.mp htTL).2
    have hNt : t ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le htT
    have hσK4 : InK4 (S.frame.ρ ⟨t, hNt⟩) :=
      InK4_of_InD _ (S.frame.T_D ⟨t, hNt⟩ htT) ((S.frame.image_L _).1 ⟨⟨t, hNt⟩, htL, rfl⟩)
    rcases InK4_cases _ hσK4 with h | h | h | h
    · exact ⟨t * (1 : G)⁻¹, hfac t htT hNt 1 T.one_mem (Subgroup.normalizer (V : Set G)).one_mem
        (h.trans (map_one S.frame.ρ).symm), 1,
        (mem_klein_iff a b ha2 hb2 hab 1).mpr (Or.inl rfl), by simp⟩
    · exact ⟨t * a⁻¹, hfac t htT hNt a haT haN (h.trans hρa.symm), a,
        (mem_klein_iff a b ha2 hb2 hab a).mpr (Or.inr (Or.inl rfl)), by simp⟩
    · exact ⟨t * b⁻¹, hfac t htT hNt b hbT hbN (h.trans hρb.symm), b,
        (mem_klein_iff a b ha2 hb2 hab b).mpr (Or.inr (Or.inr (Or.inl rfl))), by simp⟩
    · exact ⟨t * (a * b)⁻¹, hfac t htT hNt (a * b) (T.mul_mem haT hbT)
        ((Subgroup.normalizer (V : Set G)).mul_mem haN hbN) (h.trans hρab.symm), a * b,
        (mem_klein_iff a b ha2 hb2 hab (a * b)).mpr (Or.inr (Or.inr (Or.inr rfl))), by group⟩
  have hidx : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := by
    have e1 : (T ⊓ L).relIndex L = T.relIndex L := by
      have h := Subgroup.relIndex_inf_mul_relIndex T L L
      rw [inf_idem, Subgroup.relIndex_self, mul_one] at h
      exact h.symm
    have e2 : T.relIndex L = T.relIndex (L ⊔ T) := relIndex_eq_of_normal hN
    have h2 : ((T ⊓ L).subgroupOf L).index = (T ⊓ L).relIndex L := rfl
    rw [h2, e1, e2]
    exact S.sylow_LT.2.2
  have hTL2 : IsPGroup 2 (T ⊓ L : Subgroup G) := fun g => by
    obtain ⟨k, hk⟩ := S.isPGroup_T ⟨g.1, (inf_le_left : T ⊓ L ≤ T) g.2⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hVn : ∀ h ∈ L, ∀ v ∈ V, h * v * h⁻¹ ∈ V := fun h hh v hv =>
    (Subgroup.mem_normalizer_iff.mp (S.frame.L_le hh) v).mp hv
  obtain ⟨A, hAL, hAV, hVA⟩ := exists_complement_of_sylow_complement (H := L) (V := V)
    (T := T ⊓ L) (K0 := klein a b ha2 hb2 hab) hVL (le_inf S.V_le_T hVL) inf_le_right
    hVn S.isPGroup_V (fun x hx y hy => B2F.isElemAbelian_comm S.elemAbelian_V hx hy)
    hTL2 hidx hK0TL hK0V hdec
  exact ⟨A, hAL, hAV, hVA⟩

end Setting

end CFSG.GH74.QTGen4.U42
